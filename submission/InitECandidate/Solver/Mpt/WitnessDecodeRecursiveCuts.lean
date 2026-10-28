import InitECandidate.Solver.Mpt.WitnessDecodeScratch
import InitECandidate.Solver.Mpt.CurrentConstructorArena
import InitECandidate.Solver.Mpt.FailGuardReturn
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.NullaryEnvironment

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

set_option maxRecDepth 100000 in
theorem branch_allocate_shape : branchAllocate=
    .decCall (ofString "br") .one (ofString "node_new_branch") [] branchRecord := by
  simp only [branchAllocate,branchRecord,branchBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,
    seqRest,seqFirst,decRest,callRest,yesBranch,Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem extension_body_shape : extensionBody=
    .seq (.ite (.cmp .equal (field "cn" 1) (.const 0#64)) (fail 7#64) .skip) extensionAllocate := by
  have tail : extensionAllocate=.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 88#64] afterExtension := by
    unfold extensionAllocate
    rw [extension_shape]
    rfl
  rw [extension_shape,←tail]

theorem branch_body_shape : branchBody=
    .seq (.ite (.cmp .notEqual (field "sl" 1) (.const 17#64)) (fail 4#64) .skip) branchAllocate := by
  have tail : branchAllocate=.decCall (ofString "br") .one (ofString "node_new_branch") []
      (.decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88#64] afterBranchRecord) := by
    unfold branchAllocate
    rw [branch_shape]
    rfl
  rw [branch_shape,←tail]

theorem extension_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source extensionBody).2.clock≤2 := by
  rw [extension_body_shape]
  exact Fail.guard_reached_cost source _ 7#64 extensionAllocate 2 arena.code (fun _=>extension_allocate_cost source arena)

theorem extension_body_no_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source extensionBody=(some (.returned value),post)) : False := by
  rw [extension_body_shape] at normal
  have remaining := (Fail.guard_return source post _ [.const 7#64] extensionAllocate value arena.code normal).2
  exact extension_allocate_no_return source post arena value remaining

/-- The actual persistent branch-node constructor preserves the low scratch
arena, so its genuine return cannot enable the following recursive frame. -/
theorem branch_allocate_no_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source branchAllocate=(some (.returned value),post)) : False := by
  have known:=NodeConstructor.original_code .branch source.code arena.code
  change source.code.lookup (ofString "node_new_branch")=some ([],NodeConstructor.body .branch,.one) at known
  obtain ⟨callee,called⟩:=CallNormal.nullary_environment source.code.lookup (ofString "node_new_branch") (NodeConstructor.body .branch) .one known
  rw [branch_allocate_shape] at normal
  obtain ⟨funded,target,returned,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_normal source post "br" .one
    (ofString "node_new_branch") [] [] (NodeConstructor.body .branch) branchRecord callee .one rfl called value normal
  have targetArena:=NodeConstructor.current_arena .branch (callEntryStateHOLFinite source callee) target (arena.of_frame rfl) _ bodyRun
  have currentArena : CurrentStartup.ArenaState (CallNormal.continuationEntry source target "br" returned) := targetArena.of_frame rfl
  exact branch_record_no_return _ inner currentArena value remaining

theorem branch_body_no_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source branchBody=(some (.returned value),post)) : False := by
  rw [branch_body_shape] at normal
  have remaining := (Fail.guard_return source post _ [.const 4#64] branchAllocate value arena.code normal).2
  exact branch_allocate_no_return source post arena value remaining

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_allocate_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_body_cost
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_body_no_return
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_allocate_no_return
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_body_no_return
