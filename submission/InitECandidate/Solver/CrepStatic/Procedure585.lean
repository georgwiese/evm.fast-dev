import InitECandidate.Solver.CrepToLoopBound.ProgramCost
import InitECandidate.Proofs.CrepKernelComputation
import InitECandidate.Proofs.FrontendStages.Crep.Data585

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem ceiling585 : ceiling output585.2.2 ≤ 126 := by
  dsimp only [output585]
  rw [InitECandidate.Proofs.CrepKernelComputation.crepProgToHOL_function_eq]
  decide

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.ceiling585
