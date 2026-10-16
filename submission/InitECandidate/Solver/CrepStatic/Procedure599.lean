import InitECandidate.Solver.CrepToLoopBound.ProgramCost
import InitECandidate.Proofs.CrepKernelComputation
import InitECandidate.Proofs.FrontendStages.Crep.Data599

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem ceiling599 : ceiling output599.2.2 ≤ 126 := by
  dsimp only [output599]
  rw [InitECandidate.Proofs.CrepKernelComputation.crepProgToHOL_function_eq]
  decide

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.ceiling599
