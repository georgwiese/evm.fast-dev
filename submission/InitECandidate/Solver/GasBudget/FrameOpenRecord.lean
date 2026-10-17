import InitECandidate.Solver.GasBudget.FrameOpenStores

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def recordPointer (scratch : BitVec 64) : BitVec 64 := Arenas.rounded .down scratch 104#64
noncomputable def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  WitnessRadix.QueryBranch.bind (Arenas.post {source with clock := source.clock - 1} .down scratch 104#64) "rec" (recordPointer scratch)
noncomputable def cleared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  {allocated source scratch with
    memory := WitnessRadix.Zero.finalMemory source.memory (recordPointer scratch) size
    clock := source.clock - 6}
noncomputable def recordFinal (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch child parent continuation kind message : BitVec 64) :=
  let next := cleared source scratch
  {next with
    globals := (next.globals.update (ofString "ev", .val (.word child))).update (ofString "cur_cont", .val (.word (recordPointer scratch)))
    memory := WitnessRadix.WordWrites.write next.memory
      (FieldStores.writes (recordPointer scratch) (recordFields parent continuation kind message))}
noncomputable def recordClosed (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch child parent continuation kind message : BitVec 64) :=
  restore source "rec" (emptyLocalsHOLFinite (recordFinal source scratch child parent continuation kind message))

/-- Real continuation-record allocation,104-byte clear, four stores, global
activation, return and scope. The caller must supply original arena mappings;
allocation guards and all intermediate executions are derived. -/
theorem record_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower child parent continuation kind message : BitVec 64)
    (childLocal : source.locals.lookup (ofString "child") = some (.val (.word child)))
    (parentLocal : source.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (kindLocal : source.locals.lookup (ofString "kind") = some (.val (.word kind)))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)))
    (code : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (lowerAligned : lower.toNat % 8 = 0) (room : lower.toNat + 104 ≤ scratch.toNat)
    (mapped : ∀ offset, offset + 8 ≤ size → offset % 8 = 0 → source.memaddrs (WitnessRadix.byteAddress (recordPointer scratch) offset))
    (enough : 6 ≤ source.clock) :
    evaluateHOLFiniteState source recordProgram =
      (some (.returned (.val (.word child))), recordClosed source scratch child parent continuation kind message) := by
  let entered := allocated source scratch
  let ready := cleared source scratch
  have geometry := Arenas.downward_guards scratch lower 104#64 lowerAligned room
  have recordLocal : entered.locals.lookup (ofString "rec") = some (.val (.word (recordPointer scratch))) := bind_lookup_same _ _ _
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address))
      [localVar "rec", .const 104#64] = some (WitnessRadix.Zero.values (recordPointer scratch) size) := by
    simp [evalListHOLFinite, evalListHOLExact, localVar, evalHOLExact, toExact, recordLocal,
      WitnessRadix.Zero.values, size]
  have clearRun := WitnessRadix.Zero.call_execute entered [localVar "rec", .const 104#64] (recordPointer scratch) size
    args zeroCode (by decide) (by decide) geometry.2.2.2.2.2 mapped
    (by change 5 ≤ source.clock - 1; omega)
  have clocks : source.clock - 1 - (WitnessRadix.Zero.price size + 1) = source.clock - 6 := by simp [size, WitnessRadix.Zero.price]; omega
  change evaluateHOLFiniteState entered clear = (none, {entered with
    memory := WitnessRadix.Zero.finalMemory source.memory (recordPointer scratch) size
    clock := source.clock - 1 - (WitnessRadix.Zero.price size + 1)}) at clearRun
  rw [clocks] at clearRun
  change evaluateHOLFiniteState entered clear = (none, ready) at clearRun
  have readyChild : ready.locals.lookup (ofString "child") = some (.val (.word child)) :=
    (bind_lookup_other _ "rec" "child" _ (by decide)).trans childLocal
  have readyParent : ready.locals.lookup (ofString "parent") = some (.val (.word parent)) :=
    (bind_lookup_other _ "rec" "parent" _ (by decide)).trans parentLocal
  have readyKind : ready.locals.lookup (ofString "kind") = some (.val (.word kind)) :=
    (bind_lookup_other _ "rec" "kind" _ (by decide)).trans kindLocal
  have readyMessage : ready.locals.lookup (ofString "msg") = some (.val (.word message)) :=
    (bind_lookup_other _ "rec" "msg" _ (by decide)).trans messageLocal
  have readyEv : ready.globals.lookup (ofString "ev") = some (.val (.word parent)) := by
    simpa [ready, cleared, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using evGlobal
  have readyCont : ready.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)) := by
    simpa [ready, cleared, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using continuationGlobal
  have storesRun := stores_execute ready (recordPointer scratch) child parent continuation kind message recordLocal readyChild
    readyParent readyKind readyMessage readyEv readyCont (by
      intro offset member
      apply mapped
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide)
  change evaluateHOLFiniteState ready afterClear =
    (some (.returned (.val (.word child))), emptyLocalsHOLFinite (recordFinal source scratch child parent continuation kind message)) at storesRun
  have suffix := WitnessRadix.StateSteps.next_sequence entered ready clear afterClear clearRun
    (by change source.clock - 6 ≤ source.clock - 1; omega)
  rw [storesRun] at suffix
  have allocationRun := Arenas.call_execute source .down "rec" [.const 104#64] (.seq clear afterClear) scratch lower 104#64
    rfl code scratchGlobal lowerGlobal lowerAligned room (by omega)
  change evaluateHOLFiniteState source recordProgram =
    (let output := evaluateHOLFiniteState entered (.seq clear afterClear)
     (output.1, restore source "rec" output.2)) at allocationRun
  rw [suffix] at allocationRun
  exact allocationRun

/-- The continuation record lies below the just-constructed child. Its actual
clear/stores preserve all three regular ledger words of that child. -/
theorem record_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower child parent continuation kind message : BitVec 64)
    (lowerAligned : lower.toNat % 8 = 0) (room : lower.toNat + 104 ≤ scratch.toNat)
    (above : scratch.toNat ≤ child.toNat) (fits : child.toNat + 280 < 2 ^ 64) :
    regularBudget (recordClosed source scratch child parent continuation kind message).memory child =
      regularBudget source.memory child := by
  have geometry := Arenas.downward_guards scratch lower 104#64 lowerAligned room
  have endBound : (recordPointer scratch).toNat + 104 ≤ scratch.toNat := geometry.2.2.2.1
  have away (offset : Nat) (member : offset ∈ ([64, 184, 192] : List Nat)) (writeOffset : Nat) (inside : writeOffset < size) :
      child + BitVec.ofNat 64 offset ≠ WitnessRadix.byteAddress (recordPointer scratch) writeOffset := by
    change writeOffset < 104 at inside
    have offsetSmall : offset < 280 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    have first := WitnessRadix.byteAddress_toNat child offset (by omega)
    have second := WitnessRadix.byteAddress_toNat (recordPointer scratch) writeOffset (by have bound := scratch.isLt; omega)
    intro same
    have numbers := congrArg BitVec.toNat same
    change (WitnessRadix.byteAddress child offset).toNat = _ at numbers
    rw [first, second] at numbers
    omega
  have preserved (offset : Nat) (member : offset ∈ ([64, 184, 192] : List Nat)) :
      (recordClosed source scratch child parent continuation kind message).memory (child + BitVec.ofNat 64 offset) =
        source.memory (child + BitVec.ofNat 64 offset) := by
    change WitnessRadix.WordWrites.write (WitnessRadix.Zero.finalMemory source.memory (recordPointer scratch) size)
      (FieldStores.writes (recordPointer scratch) (recordFields parent continuation kind message)) _ = _
    rw [WitnessRadix.WordWrites.write_away]
    · exact WitnessRadix.Zero.final_memory_away source.memory (recordPointer scratch) _ size (away offset member)
    · simp only [FieldStores.writes, recordFields, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨away offset member 0 (by decide), away offset member 8 (by decide),
        away offset member 16 (by decide), away offset member 40 (by decide)⟩
  simp only [regularBudget, wordAt, preserved 64 (by simp), preserved 184 (by simp), preserved 192 (by simp)]

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.record_execute
#print axioms InitECandidate.Solver.GasBudget.FrameOpen.record_budget
