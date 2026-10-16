import InitECandidate.Solver.CrepStatic.Procedure752
import InitECandidate.Solver.CrepStatic.Procedure753
import InitECandidate.Solver.CrepStatic.Procedure754
import InitECandidate.Solver.CrepStatic.Procedure755
import InitECandidate.Solver.CrepStatic.Procedure756
import InitECandidate.Solver.CrepStatic.Procedure757
import InitECandidate.Solver.CrepStatic.Procedure758
import InitECandidate.Solver.CrepStatic.Procedure759
import InitECandidate.Solver.CrepStatic.Procedure760
import InitECandidate.Solver.CrepStatic.Procedure761
import InitECandidate.Solver.CrepStatic.Procedure762
import InitECandidate.Solver.CrepStatic.Procedure763
import InitECandidate.Solver.CrepStatic.Procedure764
import InitECandidate.Solver.CrepStatic.Procedure765
import InitECandidate.Solver.CrepStatic.Procedure766
import InitECandidate.Solver.CrepStatic.Procedure767
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk47 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output752, output753, output754, output755, output756, output757, output758, output759, output760, output761, output762, output763, output764, output765, output766, output767]

theorem chunk47Safe : entriesSafe 126 chunk47 = true := by
  change (decide (ceiling output752.2.2 ≤ 126) && (decide (ceiling output753.2.2 ≤ 126) && (decide (ceiling output754.2.2 ≤ 126) && (decide (ceiling output755.2.2 ≤ 126) && (decide (ceiling output756.2.2 ≤ 126) && (decide (ceiling output757.2.2 ≤ 126) && (decide (ceiling output758.2.2 ≤ 126) && (decide (ceiling output759.2.2 ≤ 126) && (decide (ceiling output760.2.2 ≤ 126) && (decide (ceiling output761.2.2 ≤ 126) && (decide (ceiling output762.2.2 ≤ 126) && (decide (ceiling output763.2.2 ≤ 126) && (decide (ceiling output764.2.2 ≤ 126) && (decide (ceiling output765.2.2 ≤ 126) && (decide (ceiling output766.2.2 ≤ 126) && (decide (ceiling output767.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling752, ceiling753, ceiling754, ceiling755, ceiling756, ceiling757, ceiling758, ceiling759, ceiling760, ceiling761, ceiling762, ceiling763, ceiling764, ceiling765, ceiling766, ceiling767, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk47Safe
