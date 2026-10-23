import InitECandidate.Solver.Mpt.CollapseBranchSuffixProgram
import InitECandidate.Solver.Input.SequenceChoice
import InitECandidate.Solver.Input.TailCallNoFallthrough

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem empty_stops : Input.NoFallthrough emptyBlock := by
  rw [value_shapes.2.2.2.1,value_shapes.2.2.2.2.2.1]
  exact .sequence _ _ (.tail_call _ _)

theorem single_stops : Input.NoFallthrough childScope := by
  rw [child_shapes.1,child_shapes.2.1,child_shapes.2.2.1,child_shapes.2.2.2.2.1,child_shapes.2.2.2.2.2.1,
    merge_shapes.1,merge_shapes.2.2.1,merge_shapes.2.2.2.1,merge_shapes.2.2.2.2.2]
  repeat first
    | apply Input.NoFallthrough.declared
    | apply Input.NoFallthrough.scoped
    | apply Input.NoFallthrough.sequence
    | exact Input.NoFallthrough.tail_call _ _

theorem single_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count length : BitVec 64)
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (lengthCell : source.locals.lookup (ofString "vl")=some (.val (.word length))) :
    eval source singleTest=some (.val (.word (if count=1#64 ∧ length=0#64 then 1#64 else 0#64))) := by
  by_cases one : count=1#64 <;> by_cases zero : length=0#64 <;>
    simp [eval,singleTest,localVar,evalHOLExact,evalListHOLExact,toExact,countCell,lengthCell,one,zero,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,valueIsWord,valueWord,wordOpHOL,wordOp] <;> decide

/-- True scalar guard dispatch, retaining all failure and timeout cases
of the selected stopping block. -/
theorem after_empty_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count length : BitVec 64)
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (lengthCell : source.locals.lookup (ofString "vl")=some (.val (.word length))) :
    evaluateHOLFiniteState source afterEmpty=if count=1#64 ∧ length=0#64 then evaluateHOLFiniteState source childScope else evaluateHOLFiniteState source footer := by
  have read:=single_test_read source count length countCell lengthCell
  simp only [eval] at read
  have guard : evaluateHOLFiniteState source singleChoice=if count=1#64 ∧ length=0#64 then evaluateHOLFiniteState source childScope else (none,source):=by
    rw [value_shapes.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_ite,read]
    by_cases chosen : count=1#64 ∧ length=0#64 <;> simp [chosen,evaluateHOLFiniteState_skip]
  rw [value_shapes.2.2.2.2.2.2.1]
  exact Input.sequence_choice source singleChoice childScope footer (count=1#64 ∧ length=0#64) guard single_stops

theorem after_value_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count length : BitVec 64)
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (lengthCell : source.locals.lookup (ofString "vl")=some (.val (.word length))) :
    evaluateHOLFiniteState source afterValue=if count=0#64 then evaluateHOLFiniteState source emptyBlock else
      if count=1#64 ∧ length=0#64 then evaluateHOLFiniteState source childScope else evaluateHOLFiniteState source footer := by
  have guard : evaluateHOLFiniteState source emptyChoice=if count=0#64 then evaluateHOLFiniteState source emptyBlock else (none,source):=by
    rw [value_shapes.2.2.1,evaluateHOLFiniteState_ite]
    by_cases chosen : count=0#64 <;> simp [evalHOLExact,toExact,localVar,countCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,chosen,evaluateHOLFiniteState_skip]
  rw [value_shapes.2.1,Input.sequence_choice source emptyChoice emptyBlock afterEmpty (count=0#64) guard empty_stops,
    after_empty_dispatch source count length countCell lengthCell]

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.empty_stops
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.single_stops
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.single_test_read
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.after_empty_dispatch
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.after_value_dispatch
