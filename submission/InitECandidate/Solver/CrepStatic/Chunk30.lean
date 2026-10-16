import InitECandidate.Solver.CrepStatic.Procedure480
import InitECandidate.Solver.CrepStatic.Procedure481
import InitECandidate.Solver.CrepStatic.Procedure482
import InitECandidate.Solver.CrepStatic.Procedure483
import InitECandidate.Solver.CrepStatic.Procedure484
import InitECandidate.Solver.CrepStatic.Procedure485
import InitECandidate.Solver.CrepStatic.Procedure486
import InitECandidate.Solver.CrepStatic.Procedure487
import InitECandidate.Solver.CrepStatic.Procedure488
import InitECandidate.Solver.CrepStatic.Procedure489
import InitECandidate.Solver.CrepStatic.Procedure490
import InitECandidate.Solver.CrepStatic.Procedure491
import InitECandidate.Solver.CrepStatic.Procedure492
import InitECandidate.Solver.CrepStatic.Procedure493
import InitECandidate.Solver.CrepStatic.Procedure494
import InitECandidate.Solver.CrepStatic.Procedure495
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk30 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output480, output481, output482, output483, output484, output485, output486, output487, output488, output489, output490, output491, output492, output493, output494, output495]

theorem chunk30Safe : entriesSafe 126 chunk30 = true := by
  change (decide (ceiling output480.2.2 ≤ 126) && (decide (ceiling output481.2.2 ≤ 126) && (decide (ceiling output482.2.2 ≤ 126) && (decide (ceiling output483.2.2 ≤ 126) && (decide (ceiling output484.2.2 ≤ 126) && (decide (ceiling output485.2.2 ≤ 126) && (decide (ceiling output486.2.2 ≤ 126) && (decide (ceiling output487.2.2 ≤ 126) && (decide (ceiling output488.2.2 ≤ 126) && (decide (ceiling output489.2.2 ≤ 126) && (decide (ceiling output490.2.2 ≤ 126) && (decide (ceiling output491.2.2 ≤ 126) && (decide (ceiling output492.2.2 ≤ 126) && (decide (ceiling output493.2.2 ≤ 126) && (decide (ceiling output494.2.2 ≤ 126) && (decide (ceiling output495.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling480, ceiling481, ceiling482, ceiling483, ceiling484, ceiling485, ceiling486, ceiling487, ceiling488, ceiling489, ceiling490, ceiling491, ceiling492, ceiling493, ceiling494, ceiling495, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk30Safe
