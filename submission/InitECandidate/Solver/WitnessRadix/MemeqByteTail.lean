import InitECandidate.Solver.WitnessRadix.MemeqByteLoop

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem byte_suffix_done {F : Type} (state : PanSemStateFiniteExact 64 F)
    (current : state.locals.lookup (ofString "i") = some (.val (.word 32#64)))
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64))) :
    evaluateHOLFiniteState state
      (.seq (.while condition1 byteBodies.2) (CompareChain.returned 1#64)) =
      (some (.returned (.val (.word 1#64))), emptyLocalsHOLFinite state) := by
  classical
  have test := eval_condition1_done state current length
  have stopped : evaluateHOLFiniteState state (.while condition1 byteBodies.2) = (none, state) := by
    rw [evaluateHOLFiniteState_while_total]
    simp only [eval, evalHOLFinite] at test ⊢
    rw [test]
    simp
  rw [evaluateHOLFiniteState_seq, stopped]
  have fixed : fixClockHOLFinite state ((none : Option (PanSemResultExact 64)), state) =
      (none, state) := by simp [fixClockHOLFinite]
  simpa only [fixed] using CompareChain.return_word state 1#64

theorem byte_tail_execute {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : Fin 4 → Fin 8 → BitVec 64)
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (ready : ByteLoopReady state left right) (clock : Nat) (enough : 4 ≤ clock) :
    ∃ paid, paid ≤ 4 ∧
      evaluateHOLFiniteState (indexed state clock 0) parts.tailCode =
        (some (.returned (.val (.word (if allBlocks left right 0 4 then 1#64 else 0#64)))),
          emptyLocalsHOLFinite { state with clock := clock - paid }) := by
  classical
  obtain ⟨paid, bound, loop⟩ := byte_loop_execute state left right length ready 4 0 clock rfl enough
  refine ⟨paid, bound, ?_⟩
  rw [tail_shape, evaluateHOLFiniteState_seq, loop]
  by_cases equal : allBlocks left right 0 4 = true
  · simp only [equal, ↓reduceIte]
    have fixed : fixClockHOLFinite (indexed state clock 0)
        ((none : Option (PanSemResultExact 64)), indexed state (clock - paid) 32) =
        (none, indexed state (clock - paid) 32) := by
      have noIncrease : ¬ clock < clock - paid := by omega
      simp [fixClockHOLFinite, indexed, QueryBranch.bind, setVarHOLFinite, noIncrease]
    rw [fixed]
    have suffix := byte_suffix_done (indexed state (clock - paid) 32)
      (indexed_current state (clock - paid) 32) (indexed_length state (clock - paid) 32 length)
    simpa [indexed, QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite] using suffix
  · have unequal : allBlocks left right 0 4 = false := Bool.eq_false_iff.mpr equal
    simp only [unequal, Bool.false_eq_true, ↓reduceIte]
    have fixed : fixClockHOLFinite (indexed state clock 0)
        ((some (.returned (.val (.word 0#64))) : Option (PanSemResultExact 64)),
          emptyLocalsHOLFinite { state with clock := clock - paid }) =
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite { state with clock := clock - paid }) := by
      have noIncrease : ¬ clock < clock - paid := by omega
      simp [fixClockHOLFinite, indexed, QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite, noIncrease]
    rw [fixed]

/-- Whole fixed memeq function through its actual unaligned byte loops. At
most four source clock units are consumed; callers still pay call entry. -/
theorem unaligned_execute {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : Fin 4 → Fin 8 → BitVec 64)
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (unaligned : eval (indexed state state.clock 0) alignmentTest = some (.val (.word 0#64)))
    (ready : ByteLoopReady state left right) (enough : 4 ≤ state.clock) :
    ∃ paid, paid ≤ 4 ∧ evaluateHOLFiniteState state body =
      (some (.returned (.val (.word (if allBlocks left right 0 4 then 1#64 else 0#64)))),
        restore state "i" (emptyLocalsHOLFinite { state with clock := state.clock - paid })) := by
  classical
  obtain ⟨paid, bound, tail⟩ := byte_tail_execute state left right length ready state.clock enough
  let initial := indexed state state.clock 0
  have skipped : evaluateHOLFiniteState initial
      (.ite alignmentTest (.seq (.ite (sizeTest 20#64) parts.twenty .skip)
        (.seq (.ite (sizeTest 32#64) parts.thirtyTwo .skip) parts.otherAligned)) .skip) =
      (none, initial) := by
    rw [evaluateHOLFiniteState_ite]
    simp only [eval] at unaligned
    simp [initial, unaligned]
  have suffix : evaluateHOLFiniteState initial
      (.seq (.ite alignmentTest (.seq (.ite (sizeTest 20#64) parts.twenty .skip)
        (.seq (.ite (sizeTest 32#64) parts.thirtyTwo .skip) parts.otherAligned)) .skip) parts.tailCode) =
      (some (.returned (.val (.word (if allBlocks left right 0 4 then 1#64 else 0#64)))),
        emptyLocalsHOLFinite { state with clock := state.clock - paid }) := by
    rw [evaluateHOLFiniteState_seq, skipped]
    have fixed : fixClockHOLFinite initial ((none : Option (PanSemResultExact 64)), initial) =
        (none, initial) := by simp [fixClockHOLFinite]
    simpa only [fixed] using tail
  refine ⟨paid, bound, ?_⟩
  rw [body_shape, evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let result := (evaluateHOLFiniteState initial
    (.seq (.ite alignmentTest (.seq (.ite (sizeTest 20#64) parts.twenty .skip)
      (.seq (.ite (sizeTest 32#64) parts.thirtyTwo .skip) parts.otherAligned)) .skip) parts.tailCode));
    (result.1, restore state "i" result.2)) = _
  rw [suffix]

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.byte_tail_execute
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.unaligned_execute
