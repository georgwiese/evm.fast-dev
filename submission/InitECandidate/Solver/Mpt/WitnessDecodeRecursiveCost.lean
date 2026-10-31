import InitECandidate.Solver.Mpt.WitnessDecodeRecursiveCuts
import InitECandidate.Solver.Mpt.NodeBranchAnyCost
import InitECandidate.Solver.Input.NullaryEnvironment

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual persistent branch-node constructor and complete scratch-frame
suffix have a fixed all-outcome cost. No recursive child is entered. -/
theorem branch_allocate_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source branchAllocate).2.clock≤231 := by
  have cost : ClockCost.Bound source.code branchAllocate 231 := by
    rw [branch_allocate_shape]
    exact ClockCost.scoped_body source.code (ofString "br") .one (ofString "node_new_branch") [] branchRecord []
      (NodeConstructor.body .branch) .one 228 2 (NodeConstructor.original_code .branch source.code arena.code)
      (NodeConstructor.branch_uniform_price source.code arena.code) (branch_record_price source.code arena.code)
  exact cost source rfl

theorem branch_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source branchBody).2.clock≤231 := by
  rw [branch_body_shape]
  exact Fail.guard_reached_cost source _ 4#64 branchAllocate 231 arena.code (fun _=>branch_allocate_cost source arena)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_allocate_cost
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_body_cost
