import InitECandidate.Solver.Mpt.WitnessDecodeRecursiveCuts
import InitECandidate.Solver.Mpt.NodeConstructorBranchCost
import InitECandidate.Solver.Input.NullaryEnvironment

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual persistent branch-node constructor and failing scratch-frame
suffix have a fixed all-outcome cost. No recursive child is entered. -/
theorem branch_allocate_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source branchAllocate).2.clock≤231 := by
  have known:=NodeConstructor.original_code .branch source.code arena.code
  change source.code.lookup (ofString "node_new_branch")=some ([],NodeConstructor.body .branch,.one) at known
  obtain ⟨callee,called⟩:=CallNormal.nullary_environment source.code.lookup (ofString "node_new_branch") (NodeConstructor.body .branch) .one known
  rw [branch_allocate_shape]
  apply ClockCost.scoped_reached_current source "br" .one (ofString "node_new_branch") [] [] (NodeConstructor.body .branch) branchRecord callee .one
    228 2 rfl called (NodeConstructor.branch_body_price (callEntryStateHOLFinite source callee) arena.code)
  intro target returned actual checked
  have targetArena:=NodeConstructor.current_arena .branch (callEntryStateHOLFinite source callee) target (arena.of_frame rfl) _ actual
  exact branch_record_cost (CallNormal.continuationEntry source target "br" returned) (targetArena.of_frame rfl)

theorem branch_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source branchBody).2.clock≤231 := by
  rw [branch_body_shape]
  exact Fail.guard_reached_cost source _ 4#64 branchAllocate 231 arena.code (fun _=>branch_allocate_cost source arena)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_allocate_cost
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_body_cost
