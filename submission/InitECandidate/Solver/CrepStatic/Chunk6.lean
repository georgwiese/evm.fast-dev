import InitECandidate.Solver.CrepStatic.Procedure96
import InitECandidate.Solver.CrepStatic.Procedure97
import InitECandidate.Solver.CrepStatic.Procedure98
import InitECandidate.Solver.CrepStatic.Procedure99
import InitECandidate.Solver.CrepStatic.Procedure100
import InitECandidate.Solver.CrepStatic.Procedure101
import InitECandidate.Solver.CrepStatic.Procedure102
import InitECandidate.Solver.CrepStatic.Procedure103
import InitECandidate.Solver.CrepStatic.Procedure104
import InitECandidate.Solver.CrepStatic.Procedure105
import InitECandidate.Solver.CrepStatic.Procedure106
import InitECandidate.Solver.CrepStatic.Procedure107
import InitECandidate.Solver.CrepStatic.Procedure108
import InitECandidate.Solver.CrepStatic.Procedure109
import InitECandidate.Solver.CrepStatic.Procedure110
import InitECandidate.Solver.CrepStatic.Procedure111
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk6 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output96, output97, output98, output99, output100, output101, output102, output103, output104, output105, output106, output107, output108, output109, output110, output111]

theorem chunk6Safe : entriesSafe 126 chunk6 = true := by
  change (decide (ceiling output96.2.2 ≤ 126) && (decide (ceiling output97.2.2 ≤ 126) && (decide (ceiling output98.2.2 ≤ 126) && (decide (ceiling output99.2.2 ≤ 126) && (decide (ceiling output100.2.2 ≤ 126) && (decide (ceiling output101.2.2 ≤ 126) && (decide (ceiling output102.2.2 ≤ 126) && (decide (ceiling output103.2.2 ≤ 126) && (decide (ceiling output104.2.2 ≤ 126) && (decide (ceiling output105.2.2 ≤ 126) && (decide (ceiling output106.2.2 ≤ 126) && (decide (ceiling output107.2.2 ≤ 126) && (decide (ceiling output108.2.2 ≤ 126) && (decide (ceiling output109.2.2 ≤ 126) && (decide (ceiling output110.2.2 ≤ 126) && (decide (ceiling output111.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling96, ceiling97, ceiling98, ceiling99, ceiling100, ceiling101, ceiling102, ceiling103, ceiling104, ceiling105, ceiling106, ceiling107, ceiling108, ceiling109, ceiling110, ceiling111, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk6Safe
