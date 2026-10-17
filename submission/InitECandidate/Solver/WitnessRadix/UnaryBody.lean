import InitECandidate.Solver.WitnessRadix.UnaryProgram
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.WitnessRadix.UnaryProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem test_read {F : Type} (source : PanSemStateFiniteExact 64 F) (zeros count : BitVec 64)
    (zeroLocal : source.locals.lookup (ofString "zeros") = some (.val (.word zeros)))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word count))) :
    eval source unaryTest = some (.val (.word (if zeros = 0#64 ∨ zeros = count then 1#64 else 0#64))) := by
  classical
  by_cases isZero : zeros = 0#64
  · subst zeros
    by_cases countZero : count = 0#64
    · subst count
      simp [eval, unaryTest, localVar, evalHOLExact, evalListHOLExact, toExact,
        zeroLocal, countLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> decide
    · simp [eval, unaryTest, localVar, evalHOLExact, evalListHOLExact, toExact,
        zeroLocal, countLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, countZero, Ne.symm countZero] <;> decide
  · by_cases isCount : zeros = count
    · subst zeros
      simp [eval, unaryTest, localVar, evalHOLExact, evalListHOLExact, toExact,
        zeroLocal, countLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, isZero] <;> decide
    · simp [eval, unaryTest, localVar, evalHOLExact, evalListHOLExact, toExact,
        zeroLocal, countLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, isZero, isCount] <;> decide
  all_goals decide

theorem body_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (bit : BitVec 64)
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word bit))) :
    evaluateHOLFiniteState source unaryBody = (some .continue, bind source "bit" (bit + 1#64)) := by
  classical
  have read : eval source (addConst (localVar "bit") 1#64) = some (.val (.word (bit + 1#64))) := by
    simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, bitLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have assignment := StateSteps.assign_execute source "bit" _ bit (bit + 1#64) bitLocal read
  rw [unaryBody, StateSteps.next_sequence source (bind source "bit" (bit + 1#64)) bitAssignment _ assignment (Nat.le_refl _)]
  rw [evaluateHOLFiniteState_continue]

/-- Actual unary path after counting: advance bit and continue, with no
memory change and no additional source-clock payment. -/
theorem after_count_unary {F : Type} (source : PanSemStateFiniteExact 64 F)
    (zeros count bit : BitVec 64)
    (zeroLocal : source.locals.lookup (ofString "zeros") = some (.val (.word zeros)))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word count)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word bit)))
    (unary : zeros = 0#64 ∨ zeros = count) :
    evaluateHOLFiniteState source afterCount = (some .continue, bind source "bit" (bit + 1#64)) := by
  classical
  have test := test_read source zeros count zeroLocal countLocal
  simp only [eval, if_pos unary] at test
  have chosen : evaluateHOLFiniteState source (.ite unaryTest unaryBody .skip) =
      (some .continue, bind source "bit" (bit + 1#64)) := by
    rw [evaluateHOLFiniteState_ite, test]
    simpa using body_execute source bit bitLocal
  rw [after_count_shape]
  exact StateSteps.stopped_sequence source (bind source "bit" (bit + 1#64)) _ _ _ chosen (Nat.le_refl _)

end InitECandidate.Solver.WitnessRadix.UnaryProgram

#print axioms InitECandidate.Solver.WitnessRadix.UnaryProgram.after_count_unary
