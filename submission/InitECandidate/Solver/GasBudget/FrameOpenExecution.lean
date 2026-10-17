import InitECandidate.Solver.GasBudget.FrameOpenRecordFrame
import InitECandidate.Solver.GasBudget.FrameOpenGeometry
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 6000 in
/-- Complete original frame_open: save parent, construct child, allocate and
initialize its actual continuation record, activate both globals and return.
Entry ownership remains explicit. This initializes the active child's regular
ledger from MSG_GAS; its price+n+44 allowance is in source clocks only. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower message empty parent continuation kind : BitVec 64) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : FrameNew.Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (known : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (kindLocal : source.locals.lookup (ofString "kind") = some (.val (.word kind)))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (enough : words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44 ≤ source.clock) :
    ∃ (target : PanSemStateFiniteExact 64 Guest.HostMemory) (spent : Nat),
      spent ≤ words.length.toNat ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word (FrameNew.framePointer scratch)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := (((source.globals.update (ofString "frame_mem_ptr", .val (.word (FrameNew.memoryPointer lower)))).update
          (ofString "scratch_ptr", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))).update
          (ofString "ev", .val (.word (FrameNew.framePointer scratch)))).update
          (ofString "cur_cont", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))
        memory := target.memory
        clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44 + spent)} ∧
      regularBudget target.memory (FrameNew.framePointer scratch) = words.gas.toNat ∧
      ∀ query, Arenas.Outside lower scratch query → target.memory query = source.memory query := by
  let declared := WitnessRadix.QueryBranch.bind source "parent" parent
  let child := FrameNew.framePointer scratch
  let nextScratch := FrameNew.finalScratch scratch words.length
  let nextLower := FrameNew.memoryPointer lower
  let record := recordPointer nextScratch
  let price := WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat)
  have declaredEntry : FrameNew.Entry declared scratch lower message empty words addresses keys addressCount keyCount :=
    entry.relocals_clock declared.locals source.clock
  have declaredMsg : declared.locals.lookup (ofString "msg") = some (.val (.word message)) :=
    (bind_lookup_other _ "parent" "msg" _ (by decide)).trans messageLocal
  have args : evalListHOLFinite declared (h := fun address => Classical.propDecidable (declared.memaddrs address)) [localVar "msg"] = some [.val (.word message)] := by
    simp [evalListHOLFinite, evalListHOLExact, localVar, evalHOLExact, toExact, declaredMsg]
  obtain ⟨childMemory, spent, spentBound, childBudget, inputsKept, outsideKept, childRun⟩ :=
    FrameNew.call_execute declared "child" [localVar "msg"] recordProgram scratch lower message empty words
      addresses keys addressCount keyCount declaredEntry args known (by change words.length.toNat + price + 38 ≤ source.clock; change words.length.toNat + price + 44 ≤ source.clock at enough; omega)
  let childSource := WitnessRadix.QueryBranch.bind {declared with
    globals := (source.globals.update (ofString "frame_mem_ptr", .val (.word nextLower))).update
      (ofString "scratch_ptr", .val (.word nextScratch))
    memory := childMemory
    clock := source.clock - (price + 38 + spent)} "child" child
  have geo := geometry scratch lower words.length entry.scratchAligned entry.lowerAligned entry.lengthFits room
  obtain ⟨frameNumber, frameAligned, stackNumber, stackAligned, memoryNumber, memoryAligned,
    frameFits, firstRoom, laterRoom, suffixRoom, stackOrder, memoryOrder⟩ :=
    FrameNew.construction_geometry scratch lower (JumpDest.bitmapBytes words.length.toNat) entry.scratchAligned entry.lowerAligned
      (JumpDest.bytes_geometry words.length.toNat).2.1 entry.room
  have recordRoom : nextLower.toNat + 104 ≤ nextScratch.toNat := geo.2.2.1
  have recordGeo := Arenas.downward_guards nextScratch nextLower 104#64 memoryAligned recordRoom
  have recordLower : nextLower.toNat ≤ record.toNat := recordGeo.2.2.1
  have recordUpper : record.toNat + 104 ≤ nextScratch.toNat := recordGeo.2.2.2.1
  have mapped : ∀ offset, offset + 8 ≤ size → offset % 8 = 0 → childSource.memaddrs (WitnessRadix.byteAddress record offset) := by
    intro offset inside aligned
    exact FrameNew.arena_mapped_subregion source lower scratch record size entry.arena
      (by dsimp [nextLower] at recordLower; omega) (by change record.toNat + 104 ≤ scratch.toNat; exact Nat.le_trans recordUpper (Nat.le_trans geo.2.2.2 (by rw [frameNumber]; omega)))
      recordGeo.2.2.2.2.2 offset inside aligned
  have readyChild : childSource.locals.lookup (ofString "child") = some (.val (.word child)) := bind_lookup_same _ _ _
  have readyParent : childSource.locals.lookup (ofString "parent") = some (.val (.word parent)) :=
    (bind_lookup_other _ "child" "parent" _ (by decide)).trans (bind_lookup_same _ _ _)
  have readyKind : childSource.locals.lookup (ofString "kind") = some (.val (.word kind)) :=
    (bind_lookup_other _ "child" "kind" _ (by decide)).trans ((bind_lookup_other _ "parent" "kind" _ (by decide)).trans kindLocal)
  have readyMessage : childSource.locals.lookup (ofString "msg") = some (.val (.word message)) :=
    (bind_lookup_other _ "child" "msg" _ (by decide)).trans declaredMsg
  have readyEv : childSource.globals.lookup (ofString "ev") = some (.val (.word parent)) := by
    simpa [childSource, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using evGlobal
  have readyCont : childSource.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)) := by
    simpa [childSource, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using continuationGlobal
  have readyScratch : childSource.globals.lookup (ofString "scratch_ptr") = some (.val (.word nextScratch)) := by
    simp [childSource, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have readyLower : childSource.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word nextLower)) := by
    simp [childSource, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]
  have recordRun := record_execute childSource nextScratch nextLower child parent continuation kind message readyChild readyParent
    readyKind readyMessage readyEv readyCont readyScratch readyLower entry.code.scratch entry.code.zero memoryAligned recordRoom mapped
    (by change 6 ≤ source.clock - (price + 38 + spent); change words.length.toNat + price + 44 ≤ source.clock at enough; omega)
  change evaluateHOLFiniteState declared (.decCall (ofString "child") .one (ofString "frame_new") [localVar "msg"] recordProgram) =
    (let output := evaluateHOLFiniteState childSource recordProgram
     (output.1, restore declared "child" output.2)) at childRun
  rw [recordRun] at childRun
  have parentRead : eval source (.var .global (ofString "ev")) = some (.val (.word parent)) := by
    simpa only [eval, evalHOLExact, toExact] using evGlobal
  have whole := Input.ScalarScope.declare_execute source _ "parent" (.var .global (ofString "ev")) parent
    (.decCall (ofString "child") .one (ofString "frame_new") [localVar "msg"] recordProgram) _ parentRead childRun
  let target := restore source "parent" (restore declared "child" (recordClosed childSource nextScratch child parent continuation kind message))
  refine ⟨target, spent, spentBound, ?_, ?_, ?_, ?_⟩
  · rw [body_shape]
    exact whole
  · have clocks : source.clock - (price + 38 + spent) - 6 = source.clock - (price + 44 + spent) := by omega
    have overwrite : ((source.globals.update (ofString "frame_mem_ptr", .val (.word nextLower))).update
        (ofString "scratch_ptr", .val (.word nextScratch))).update (ofString "scratch_ptr", .val (.word record)) =
        (source.globals.update (ofString "frame_mem_ptr", .val (.word nextLower))).update (ofString "scratch_ptr", .val (.word record)) := by
      apply HolFiniteMapExact.ext
      funext query
      by_cases same : ofString "scratch_ptr" = query <;> simp [HolFiniteMapExact.update, FUPDATE, same]
    change emptyLocalsHOLFinite {source with
      globals := ((((source.globals.update (ofString "frame_mem_ptr", .val (.word nextLower))).update
        (ofString "scratch_ptr", .val (.word nextScratch))).update (ofString "scratch_ptr", .val (.word record))).update
        (ofString "ev", .val (.word child))).update (ofString "cur_cont", .val (.word record))
      memory := target.memory
      clock := source.clock - (price + 38 + spent) - 6} = _
    rw [overwrite, clocks]
  · exact (record_budget childSource nextScratch nextLower child parent continuation kind message memoryAligned recordRoom geo.2.2.2 frameFits).trans childBudget
  · intro query outside
    have nextOutside : Arenas.Outside nextLower nextScratch query := by
      rcases outside with below | high
      · exact Or.inl (Nat.lt_of_lt_of_le below (by change lower.toNat ≤ (FrameNew.memoryPointer lower).toNat; rw [memoryNumber]; omega))
      · exact Or.inr (Nat.le_trans geo.2.2.2 (Nat.le_trans (by rw [frameNumber]; omega) high))
    change (recordClosed childSource nextScratch child parent continuation kind message).memory query = source.memory query
    rw [record_memory_outside childSource nextScratch nextLower child parent continuation kind message query memoryAligned recordRoom nextOutside]
    exact outsideKept query outside

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.execute
