import InitECandidate.Solver.CrepStatic.Procedure672
import InitECandidate.Solver.CrepStatic.Procedure673
import InitECandidate.Solver.CrepStatic.Procedure674
import InitECandidate.Solver.CrepStatic.Procedure675
import InitECandidate.Solver.CrepStatic.Procedure676
import InitECandidate.Solver.CrepStatic.Procedure677
import InitECandidate.Solver.CrepStatic.Procedure678
import InitECandidate.Solver.CrepStatic.Procedure679
import InitECandidate.Solver.CrepStatic.Procedure680
import InitECandidate.Solver.CrepStatic.Procedure681
import InitECandidate.Solver.CrepStatic.Procedure682
import InitECandidate.Solver.CrepStatic.Procedure683
import InitECandidate.Solver.CrepStatic.Procedure684
import InitECandidate.Solver.CrepStatic.Procedure685
import InitECandidate.Solver.CrepStatic.Procedure686
import InitECandidate.Solver.CrepStatic.Procedure687
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk42 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output672, output673, output674, output675, output676, output677, output678, output679, output680, output681, output682, output683, output684, output685, output686, output687]

theorem chunk42Safe : entriesSafe 126 chunk42 = true := by
  change (decide (ceiling output672.2.2 ≤ 126) && (decide (ceiling output673.2.2 ≤ 126) && (decide (ceiling output674.2.2 ≤ 126) && (decide (ceiling output675.2.2 ≤ 126) && (decide (ceiling output676.2.2 ≤ 126) && (decide (ceiling output677.2.2 ≤ 126) && (decide (ceiling output678.2.2 ≤ 126) && (decide (ceiling output679.2.2 ≤ 126) && (decide (ceiling output680.2.2 ≤ 126) && (decide (ceiling output681.2.2 ≤ 126) && (decide (ceiling output682.2.2 ≤ 126) && (decide (ceiling output683.2.2 ≤ 126) && (decide (ceiling output684.2.2 ≤ 126) && (decide (ceiling output685.2.2 ≤ 126) && (decide (ceiling output686.2.2 ≤ 126) && (decide (ceiling output687.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling672, ceiling673, ceiling674, ceiling675, ceiling676, ceiling677, ceiling678, ceiling679, ceiling680, ceiling681, ceiling682, ceiling683, ceiling684, ceiling685, ceiling686, ceiling687, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk42Safe
