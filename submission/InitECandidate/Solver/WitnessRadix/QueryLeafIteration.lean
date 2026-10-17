import InitECandidate.Solver.WitnessRadix.QueryLeafStep

namespace InitECandidate.Solver.WitnessRadix.QueryLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem leaf_test_odd {F : Type} (source : PanSemStateFiniteExact 64 F)
    (root : BitVec 64)
    (node : source.locals.lookup (ofString "node") = some (.val (.word root)))
    (odd : root &&& 1#64 = 1#64) : eval source leafTest = some (.val (.word 1#64)) := by
  classical
  have andOnes (word : BitVec 64) :
      AndOp.and word (18446744073709551615#64) = word := by
    change word &&& BitVec.allOnes 64 = word
    exact BitVec.and_allOnes
  simp [eval, leafTest, localVar, evalHOLExact, evalListHOLExact, toExact, node,
    valueIsWord, valueWord, wordOpHOL, wordOp, andOnes, odd,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  change root &&& 1#64 ≠ 0#64
  rw [odd]
  decide

/-- Propagating a read-only return through a sequence includes the actual
fix_clock operation. No monotonic-clock assumption is added. -/
theorem return_sequence {F : Type} (source : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (value : ValueHOL 64) (paid : Nat)
    (returned : (evaluateHOLFiniteState source first).1 = some (.returned value))
    (frame : emptyLocalsHOLFinite (evaluateHOLFiniteState source first).2 =
      emptyLocalsHOLFinite { source with clock := source.clock - paid }) :
    (evaluateHOLFiniteState source (.seq first second)).1 = some (.returned value) ∧
    emptyLocalsHOLFinite (evaluateHOLFiniteState source (.seq first second)).2 =
      emptyLocalsHOLFinite { source with clock := source.clock - paid } := by
  classical
  have clockEq := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) frame
  change (evaluateHOLFiniteState source first).2.clock = source.clock - paid at clockEq
  have notGreater : ¬ source.clock < (evaluateHOLFiniteState source first).2.clock := by omega
  rw [evaluateHOLFiniteState_seq]
  simp only [fixClockHOLFinite, returned, notGreater, ↓reduceIte]
  exact ⟨True.intro, frame⟩

/-- The surrounding leaf-test and sequence take the already proved actual
leaf body, return immediately and never reach the branch loads. -/
theorem leaf_iteration {F : Type} (source : PanSemStateFiniteExact 64 F)
    (root : BitVec 64) (value : ValueHOL 64) (paid : Nat)
    (node : source.locals.lookup (ofString "node") = some (.val (.word root)))
    (odd : root &&& 1#64 = 1#64)
    (returned : (evaluateHOLFiniteState source leafCode).1 = some (.returned value))
    (frame : emptyLocalsHOLFinite (evaluateHOLFiniteState source leafCode).2 =
      emptyLocalsHOLFinite { source with clock := source.clock - paid }) :
    (evaluateHOLFiniteState source QueryEmpty.loopBody).1 = some (.returned value) ∧
    emptyLocalsHOLFinite (evaluateHOLFiniteState source QueryEmpty.loopBody).2 =
      emptyLocalsHOLFinite { source with clock := source.clock - paid } := by
  classical
  have test := leaf_test_odd source root node odd
  simp only [eval] at test
  have chosen : evaluateHOLFiniteState source (.ite leafTest leafCode .skip) =
      evaluateHOLFiniteState source leafCode := by
    rw [evaluateHOLFiniteState_ite, test]
    simp
  rw [loop_shape]
  apply return_sequence
  · rw [chosen]
    exact returned
  · rw [chosen]
    exact frame

end InitECandidate.Solver.WitnessRadix.QueryLeaf

#print axioms InitECandidate.Solver.WitnessRadix.QueryLeaf.leaf_iteration
