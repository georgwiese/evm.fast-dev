import InitECandidate.Solver.CrepToLoopBound.ProgramCost
import InitECandidate.Proofs.FrontendStages.Crep.Data636

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem ceiling636 : ceiling output636.2.2 ≤ 126 := by decide

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.ceiling636
