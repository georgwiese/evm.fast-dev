import InitECandidate.Solver.CrepStatic.Procedure512
import InitECandidate.Solver.CrepStatic.Procedure513
import InitECandidate.Solver.CrepStatic.Procedure514
import InitECandidate.Solver.CrepStatic.Procedure515
import InitECandidate.Solver.CrepStatic.Procedure516
import InitECandidate.Solver.CrepStatic.Procedure517
import InitECandidate.Solver.CrepStatic.Procedure518
import InitECandidate.Solver.CrepStatic.Procedure519
import InitECandidate.Solver.CrepStatic.Procedure520
import InitECandidate.Solver.CrepStatic.Procedure521
import InitECandidate.Solver.CrepStatic.Procedure522
import InitECandidate.Solver.CrepStatic.Procedure523
import InitECandidate.Solver.CrepStatic.Procedure524
import InitECandidate.Solver.CrepStatic.Procedure525
import InitECandidate.Solver.CrepStatic.Procedure526
import InitECandidate.Solver.CrepStatic.Procedure527
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk32 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output512, output513, output514, output515, output516, output517, output518, output519, output520, output521, output522, output523, output524, output525, output526, output527]

theorem chunk32Safe : entriesSafe 126 chunk32 = true := by
  change (decide (ceiling output512.2.2 ≤ 126) && (decide (ceiling output513.2.2 ≤ 126) && (decide (ceiling output514.2.2 ≤ 126) && (decide (ceiling output515.2.2 ≤ 126) && (decide (ceiling output516.2.2 ≤ 126) && (decide (ceiling output517.2.2 ≤ 126) && (decide (ceiling output518.2.2 ≤ 126) && (decide (ceiling output519.2.2 ≤ 126) && (decide (ceiling output520.2.2 ≤ 126) && (decide (ceiling output521.2.2 ≤ 126) && (decide (ceiling output522.2.2 ≤ 126) && (decide (ceiling output523.2.2 ≤ 126) && (decide (ceiling output524.2.2 ≤ 126) && (decide (ceiling output525.2.2 ≤ 126) && (decide (ceiling output526.2.2 ≤ 126) && (decide (ceiling output527.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling512, ceiling513, ceiling514, ceiling515, ceiling516, ceiling517, ceiling518, ceiling519, ceiling520, ceiling521, ceiling522, ceiling523, ceiling524, ceiling525, ceiling526, ceiling527, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk32Safe
