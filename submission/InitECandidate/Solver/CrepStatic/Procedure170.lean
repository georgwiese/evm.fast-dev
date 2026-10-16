import InitECandidate.Solver.CrepToLoopBound.ProgramCost
import InitECandidate.Proofs.FrontendStages.Crep.Data170

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem ceiling170 : ceiling output170.2.2 ≤ 126 := by decide

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.ceiling170
