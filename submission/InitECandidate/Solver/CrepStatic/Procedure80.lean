import InitECandidate.Solver.CrepToLoopBound.ProgramCost
import InitECandidate.Proofs.FrontendStages.Crep.Data80

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem ceiling80 : ceiling output80.2.2 ≤ 126 := by decide

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.ceiling80
