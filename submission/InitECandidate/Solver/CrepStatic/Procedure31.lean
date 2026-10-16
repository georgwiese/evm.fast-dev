import InitECandidate.Solver.CrepToLoopBound.ProgramCost
import InitECandidate.Proofs.FrontendStages.Crep.Data31

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem ceiling31 : ceiling output31.2.2 ≤ 126 := by decide

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.ceiling31
