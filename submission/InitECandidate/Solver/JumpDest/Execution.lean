import InitECandidate.Solver.JumpDest.Loop
import InitECandidate.Solver.Arenas.Region

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

noncomputable def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch length : BitVec 64) :=
  WitnessRadix.QueryBranch.bind (Arenas.post {source with clock := source.clock - 1} .down scratch (bytesWord length))
    "bm" (Arenas.rounded .down scratch (bytesWord length))
noncomputable def cleared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch length : BitVec 64) :=
  {allocated source scratch length with
    memory := WitnessRadix.Zero.finalMemory source.memory (Arenas.rounded .down scratch (bytesWord length)) (bitmapBytes length.toNat)
    clock := (allocated source scratch length).clock - (WitnessRadix.Zero.price (bitmapBytes length.toNat) + 1)}
noncomputable def scanning (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch length : BitVec 64) :=
  WitnessRadix.QueryBranch.bind (cleared source scratch length) "pc" 0#64

/-- Full unchanged compute_jumpdests body: actual scratch allocation, actual
bitmap clear, complete content-independent scan, return and both scopes.
Its exact body clocks are bitmap-clear price + 2 + scan iterations, with scan
iterations at most code length. All words outside the live allocation arena
are preserved. This is a source execution contract, not a target work price. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory code length : BitVec 64)
    (scratchCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (codeLocal : source.locals.lookup (ofString "code") = some (.val (.word code)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word length)))
    (aligned : memory.toNat % 8 = 0) (fits : length.toNat + 63 < 2 ^ 64)
    (room : memory.toNat + bitmapBytes length.toNat ≤ scratch.toNat)
    (codeMapped : ∀ offset < length.toNat,
      source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress code offset)))
    (bitmapMapped : ∀ offset, offset + 8 ≤ bitmapBytes length.toNat → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress (Arenas.rounded .down scratch (bytesWord length)) offset))
    (enough : length.toNat + WitnessRadix.Zero.price (bitmapBytes length.toNat) + 2 ≤ source.clock) :
    ∃ (target : PanSemStateFiniteExact 64 Guest.HostMemory) (spent : Nat),
      spent ≤ length.toNat ∧
      evaluateHOLFiniteState source body =
        (some (.returned (.val (.word (Arenas.rounded .down scratch (bytesWord length))))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite
        {Arenas.post source .down scratch (bytesWord length) with
          memory := target.memory
          clock := source.clock - (WitnessRadix.Zero.price (bitmapBytes length.toNat) + 2 + spent)} ∧
      ∀ query : BitVec 64, Arenas.Outside memory scratch query → target.memory query = source.memory query := by
  classical
  let bitmap := Arenas.rounded .down scratch (bytesWord length)
  let bytes := bitmapBytes length.toNat
  change length.toNat + WitnessRadix.Zero.price bytes + 2 ≤ source.clock at enough
  have number := bytes_number length fits
  have wordOfBytes : BitVec.ofNat 64 bytes = bytesWord length := by
    change BitVec.ofNat 64 (bitmapBytes length.toNat) = bytesWord length
    rw [← number]
    simp [BitVec.ofNat_toNat]
  have roomWord : Arenas.Room .down scratch memory (bytesWord length) := by
    change memory.toNat + (bytesWord length).toNat ≤ scratch.toNat
    rw [number]
    exact room
  have geometry := Arenas.downward_guards scratch memory (bytesWord length) aligned roomWord
  have bytesSmall : bytes + 32 < 2 ^ 64 := by
    dsimp [bytes, bitmapBytes]
    omega
  have allocRead := bytes_read source length lengthLocal
  simp only [eval] at allocRead
  have argsAlloc : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [bytesExpression] = some [.val (.word (bytesWord length))] := by
    simp only [evalListHOLFinite, evalListHOLExact, allocRead]
  have calledAlloc := Arenas.call_execute source .down "bm" [bytesExpression] (.seq clear afterClear)
    scratch memory (bytesWord length) argsAlloc scratchCode scratchGlobal memoryGlobal aligned roomWord (by omega)
  change evaluateHOLFiniteState source program =
    (let output := evaluateHOLFiniteState (allocated source scratch length) (.seq clear afterClear)
     (output.1, restore source "bm" output.2)) at calledAlloc
  have bmA : (allocated source scratch length).locals.lookup (ofString "bm") = some (.val (.word bitmap)) := bind_lookup_same _ _ _
  have nA : (allocated source scratch length).locals.lookup (ofString "n") = some (.val (.word length)) :=
    (bind_lookup_other _ "bm" "n" _ (by decide)).trans lengthLocal
  have bytesA := bytes_read (allocated source scratch length) length nA
  have bmRead : eval (allocated source scratch length) (localVar "bm") = some (.val (.word bitmap)) := by
    simp [eval, localVar, evalHOLExact, toExact, bmA]
  simp only [eval] at bytesA bmRead
  have argsZero : evalListHOLFinite (allocated source scratch length)
      (h := fun address => Classical.propDecidable ((allocated source scratch length).memaddrs address))
      [localVar "bm", bytesExpression] = some (WitnessRadix.Zero.values bitmap bytes) := by
    simp only [evalListHOLFinite, evalListHOLExact, bmRead, bytesA, WitnessRadix.Zero.values, wordOfBytes]
  have calledZero := WitnessRadix.Zero.call_execute (allocated source scratch length) [localVar "bm", bytesExpression]
    bitmap bytes argsZero zeroCode bytesSmall (bytes_geometry length.toNat).1 geometry.2.2.2.2.2 bitmapMapped
    (by change WitnessRadix.Zero.price bytes + 1 ≤ source.clock - 1; omega)
  change evaluateHOLFiniteState (allocated source scratch length) clear = (none, cleared source scratch length) at calledZero
  have bmS : (scanning source scratch length).locals.lookup (ofString "bm") = some (.val (.word bitmap)) :=
    (bind_lookup_other _ "pc" "bm" _ (by decide)).trans bmA
  have codeA : (allocated source scratch length).locals.lookup (ofString "code") = some (.val (.word code)) :=
    (bind_lookup_other _ "bm" "code" _ (by decide)).trans codeLocal
  have codeS : (scanning source scratch length).locals.lookup (ofString "code") = some (.val (.word code)) :=
    (bind_lookup_other _ "pc" "code" _ (by decide)).trans codeA
  have nS : (scanning source scratch length).locals.lookup (ofString "n") = some (.val (.word length)) :=
    (bind_lookup_other _ "pc" "n" _ (by decide)).trans nA
  obtain ⟨finalMemory, finish, spent, loopRun, stopped, spentBound, protectedWords⟩ :=
    loop_execute_outside (scanning source scratch length) bitmap code 0#64 length bmS codeS (bind_lookup_same _ _ _) nS
      (by omega) codeMapped bitmapMapped
      (by change length.toNat - 0 ≤ source.clock - 1 - (WitnessRadix.Zero.price bytes + 1); omega)
  let finished := loopState (scanning source scratch length) finalMemory spent finish
  have bmF : finished.locals.lookup (ofString "bm") = some (.val (.word bitmap)) :=
    (bind_lookup_other _ "pc" "bm" _ (by decide)).trans bmS
  have returned : evaluateHOLFiniteState finished (.return (localVar "bm")) =
      (some (.returned (.val (.word bitmap))), emptyLocalsHOLFinite finished) := by
    simp [evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, bmF, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have tailRun := WitnessRadix.StateSteps.next_sequence (scanning source scratch length) finished loop
    (.return (localVar "bm")) loopRun (by change (scanning source scratch length).clock - spent ≤ _; omega)
  rw [returned] at tailRun
  have pcScope := Input.ScalarScope.declare_execute (cleared source scratch length) _ "pc" (.const 0#64) 0#64
    (.seq loop (.return (localVar "bm"))) (some (.returned (.val (.word bitmap)))) rfl tailRun
  change evaluateHOLFiniteState (cleared source scratch length) afterClear = _ at pcScope
  have afterAlloc := WitnessRadix.StateSteps.next_sequence (allocated source scratch length) (cleared source scratch length)
    clear afterClear calledZero (by change (allocated source scratch length).clock - _ ≤ _; omega)
  rw [pcScope] at afterAlloc
  rw [afterAlloc] at calledAlloc
  let target := restore source "bm" (restore (cleared source scratch length) "pc" (emptyLocalsHOLFinite finished))
  refine ⟨target, spent, ?_, ?_, ?_, ?_⟩
  · simpa using spentBound
  · rw [body_shape]
    exact calledAlloc
  · have clocks : source.clock - 1 - (WitnessRadix.Zero.price bytes + 1) - spent =
        source.clock - (WitnessRadix.Zero.price bytes + 2 + spent) := by omega
    exact congrArg (fun clock => emptyLocalsHOLFinite
      {Arenas.post source .down scratch (bytesWord length) with memory := finalMemory, clock := clock}) clocks
  · intro query outsideArena
    have bitmapEnd : bitmap.toNat + bytes ≤ scratch.toNat := by simpa only [number] using geometry.2.2.2.1
    have bitmapLow : memory.toNat ≤ bitmap.toNat := geometry.2.2.1
    have away : Outside bitmap bytes query := by
      rcases outsideArena with below | above
      · apply outside_below bitmap query bytes (by omega)
        have bound := scratch.isLt
        omega
      · exact outside_above bitmap query bytes (by omega)
    have clearedAway := WitnessRadix.Zero.final_memory_away source.memory bitmap query bytes away
    exact (protectedWords query away).trans clearedAway

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.execute
