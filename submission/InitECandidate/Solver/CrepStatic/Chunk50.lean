import InitECandidate.Solver.CrepStatic.Procedure800
import InitECandidate.Solver.CrepStatic.Procedure801
import InitECandidate.Solver.CrepStatic.Procedure802
import InitECandidate.Solver.CrepStatic.Procedure803
import InitECandidate.Solver.CrepStatic.Procedure804
import InitECandidate.Solver.CrepStatic.Procedure805
import InitECandidate.Solver.CrepStatic.Procedure806
import InitECandidate.Solver.CrepStatic.Procedure807
import InitECandidate.Solver.CrepStatic.Procedure808
import InitECandidate.Solver.CrepStatic.Procedure809
import InitECandidate.Solver.CrepStatic.Procedure810
import InitECandidate.Solver.CrepStatic.Procedure811
import InitECandidate.Solver.CrepStatic.Procedure812
import InitECandidate.Solver.CrepStatic.Procedure813
import InitECandidate.Solver.CrepStatic.Procedure814
import InitECandidate.Solver.CrepStatic.Procedure815
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk50 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output800, output801, output802, output803, output804, output805, output806, output807, output808, output809, output810, output811, output812, output813, output814, output815]

theorem chunk50Safe : entriesSafe 126 chunk50 = true := by
  change (decide (ceiling output800.2.2 ≤ 126) && (decide (ceiling output801.2.2 ≤ 126) && (decide (ceiling output802.2.2 ≤ 126) && (decide (ceiling output803.2.2 ≤ 126) && (decide (ceiling output804.2.2 ≤ 126) && (decide (ceiling output805.2.2 ≤ 126) && (decide (ceiling output806.2.2 ≤ 126) && (decide (ceiling output807.2.2 ≤ 126) && (decide (ceiling output808.2.2 ≤ 126) && (decide (ceiling output809.2.2 ≤ 126) && (decide (ceiling output810.2.2 ≤ 126) && (decide (ceiling output811.2.2 ≤ 126) && (decide (ceiling output812.2.2 ≤ 126) && (decide (ceiling output813.2.2 ≤ 126) && (decide (ceiling output814.2.2 ≤ 126) && (decide (ceiling output815.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling800, ceiling801, ceiling802, ceiling803, ceiling804, ceiling805, ceiling806, ceiling807, ceiling808, ceiling809, ceiling810, ceiling811, ceiling812, ceiling813, ceiling814, ceiling815, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk50Safe
