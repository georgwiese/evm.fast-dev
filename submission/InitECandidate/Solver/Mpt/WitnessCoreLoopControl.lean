import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.WitnessCoreDecodeProgram
import InitECandidate.Solver.Mpt.WitnessCoreResolveProgram
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Current236's literal loop body has no escaping caller return,
break or continue, and preserves db on normal continuation. Helper calls
may still fail or trap; no assumption about their termination is used. -/
theorem loop_body_prefix : Input.LocalPrefix (ofString "db") loopBody := by
  rw [mode_shape,decode_shape,after_decode_shape,terminal_shape,push_shape,
    resolve_shape,resolve_call_shape,after_resolve_shape,resolve_terminal_shape,resolve_decode_shape,
    return_shape,finish_return_shape,active_return_shape,after_return_hash_shape,cache_return_hash_shape,
    return_stages_shape,return_extension_shape,extension_kind_read_shape,after_extension_kind_shape,
    extension_create_shape,after_extension_create_shape,return_branch_node_shape,branch_index_read_shape,
    branch_children_shape,branch_after_child_shape,branch_after_occupancy_shape,branch_index_choice_shape,
    branch_advance_shape,branch_finish_shape,branch_value_call_shape,after_branch_value_shape,
    branch_value_body_shape,branch_value_writes_shape,branch_finish_tail_shape,branch_metadata_shape]
  simp only [pushLink,pushTop,pushSlot,pushMode,parentMetadata,popWith,returnFail,writeAt]
  repeat' first
    | apply Input.LocalPrefix.ite
    | apply Input.LocalPrefix.seq
    | apply Input.LocalPrefix.dec
    | apply Input.LocalPrefix.decCall
    | apply Input.LocalPrefix.assign
    | apply Input.LocalPrefix.store
    | exact Input.LocalPrefix.skip
    | exact Input.LocalPrefix.call none _ _ (by intro name impossible; cases impossible)
    | (solve | decide)

theorem loop_body_no_continue (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source loopBody).1≠some .continue := (loop_body_prefix.summary_full source).2.2.2

theorem loop_body_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (mode : BitVec 64)
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word mode))) :
    evaluateHOLFiniteState source loopBody=
      if mode=1#64 then evaluateHOLFiniteState source decodeBranch else
      if mode=2#64 then evaluateHOLFiniteState source resolveBranch else evaluateHOLFiniteState source returnBranch := by
  rw [mode_shape,evaluateHOLFiniteState_ite]
  by_cases one : mode=1#64
  · simp [modeTest,evalHOLExact,localVar,toExact,modeCell,one,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp only [modeTest,evalHOLExact,localVar,toExact,modeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,one,↓reduceIte]
    rw [evaluateHOLFiniteState_ite]
    by_cases two : mode=2#64 <;> simp [modeTest,evalHOLExact,localVar,toExact,modeCell,two,one,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.loop_body_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessCore.loop_body_no_continue
#print axioms InitECandidate.Solver.Mpt.WitnessCore.loop_body_choice
