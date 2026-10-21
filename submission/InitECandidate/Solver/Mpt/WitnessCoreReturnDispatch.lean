import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem return_stages_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db : BitVec 64)
    (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record))) :
    evaluateHOLFiniteState source returnStages=match data.payload with
      | .extension ..=>evaluateHOLFiniteState source returnExtension
      | .branch ..=>evaluateHOLFiniteState source returnBranchNode := by
  have mapped : source.memaddrs (record+8#64):=by simpa only [byteAddress] using view.mapped source record db data 8 (by decide) (by decide)
  have stored:=view.stage source record db data
  rw [return_stages_shape,evaluateHOLFiniteState_ite]
  cases payloadEq : data.payload <;>
    simp [readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,mapped,stored,payloadEq,WitnessRecord.Payload.stage,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem return_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record))) :
    evaluateHOLFiniteState source returnBranch=
      if record=0#64 then evaluateHOLFiniteState source finishReturn else evaluateHOLFiniteState source activeReturn := by
  rw [return_shape,evaluateHOLFiniteState_ite]
  by_cases zero : record=0#64 <;>
    simp [evalHOLExact,localVar,toExact,topCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem finish_return_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (go : BitVec 64)
    (goCell : source.locals.lookup (ofString "go")=some (.val (.word go))) :
    evaluateHOLFiniteState source finishReturn=(none,QueryBranch.bind source "go" 0#64) := by
  rw [finish_return_shape]
  exact StateSteps.assign_execute source "go" (.const 0#64) go 0#64 goCell rfl

/-- The active path reads the actual initialized pending-hash word. Its
real lexical scope is retained for arbitrary outcomes of the return tail. -/
theorem active_return_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (record db hash : BitVec 64)
    (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (hashCell : source.memory (record+80#64)=.word hash) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source activeReturn=(result,post)) :
    ∃ inner,evaluateHOLFiniteState (QueryBranch.bind source "hash" hash) afterReturnHash=(result,inner) ∧ post=restore source "hash" inner := by
  have mapped : source.memaddrs (record+80#64):=by simpa only [byteAddress] using view.mapped source record db data 80 (by decide) (by decide)
  have read : eval source (readAt "top" 80#64)=some (.val (.word hash)):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,mapped,hashCell]
  rw [active_return_shape] at run
  exact Input.ScalarScope.declare_trace source post "hash" (readAt "top" 80#64) hash afterReturnHash result read run

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_stages_choice
#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_choice
#print axioms InitECandidate.Solver.Mpt.WitnessCore.finish_return_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.active_return_trace
