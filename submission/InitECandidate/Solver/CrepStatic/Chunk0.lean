import InitECandidate.Solver.CrepStatic.Procedure0
import InitECandidate.Solver.CrepStatic.Procedure1
import InitECandidate.Solver.CrepStatic.Procedure2
import InitECandidate.Solver.CrepStatic.Procedure3
import InitECandidate.Solver.CrepStatic.Procedure4
import InitECandidate.Solver.CrepStatic.Procedure5
import InitECandidate.Solver.CrepStatic.Procedure6
import InitECandidate.Solver.CrepStatic.Procedure7
import InitECandidate.Solver.CrepStatic.Procedure8
import InitECandidate.Solver.CrepStatic.Procedure9
import InitECandidate.Solver.CrepStatic.Procedure10
import InitECandidate.Solver.CrepStatic.Procedure11
import InitECandidate.Solver.CrepStatic.Procedure12
import InitECandidate.Solver.CrepStatic.Procedure13
import InitECandidate.Solver.CrepStatic.Procedure14
import InitECandidate.Solver.CrepStatic.Procedure15
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk0 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output0, output1, output2, output3, output4, output5, output6, output7, output8, output9, output10, output11, output12, output13, output14, output15]

theorem chunk0Safe : entriesSafe 126 chunk0 = true := by
  change (decide (ceiling output0.2.2 ≤ 126) && (decide (ceiling output1.2.2 ≤ 126) && (decide (ceiling output2.2.2 ≤ 126) && (decide (ceiling output3.2.2 ≤ 126) && (decide (ceiling output4.2.2 ≤ 126) && (decide (ceiling output5.2.2 ≤ 126) && (decide (ceiling output6.2.2 ≤ 126) && (decide (ceiling output7.2.2 ≤ 126) && (decide (ceiling output8.2.2 ≤ 126) && (decide (ceiling output9.2.2 ≤ 126) && (decide (ceiling output10.2.2 ≤ 126) && (decide (ceiling output11.2.2 ≤ 126) && (decide (ceiling output12.2.2 ≤ 126) && (decide (ceiling output13.2.2 ≤ 126) && (decide (ceiling output14.2.2 ≤ 126) && (decide (ceiling output15.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling0, ceiling1, ceiling2, ceiling3, ceiling4, ceiling5, ceiling6, ceiling7, ceiling8, ceiling9, ceiling10, ceiling11, ceiling12, ceiling13, ceiling14, ceiling15, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk0Safe
