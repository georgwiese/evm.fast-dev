import InitECandidate.Solver.CrepStatic.Procedure64
import InitECandidate.Solver.CrepStatic.Procedure65
import InitECandidate.Solver.CrepStatic.Procedure66
import InitECandidate.Solver.CrepStatic.Procedure67
import InitECandidate.Solver.CrepStatic.Procedure68
import InitECandidate.Solver.CrepStatic.Procedure69
import InitECandidate.Solver.CrepStatic.Procedure70
import InitECandidate.Solver.CrepStatic.Procedure71
import InitECandidate.Solver.CrepStatic.Procedure72
import InitECandidate.Solver.CrepStatic.Procedure73
import InitECandidate.Solver.CrepStatic.Procedure74
import InitECandidate.Solver.CrepStatic.Procedure75
import InitECandidate.Solver.CrepStatic.Procedure76
import InitECandidate.Solver.CrepStatic.Procedure77
import InitECandidate.Solver.CrepStatic.Procedure78
import InitECandidate.Solver.CrepStatic.Procedure79
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk4 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output64, output65, output66, output67, output68, output69, output70, output71, output72, output73, output74, output75, output76, output77, output78, output79]

theorem chunk4Safe : entriesSafe 126 chunk4 = true := by
  change (decide (ceiling output64.2.2 ≤ 126) && (decide (ceiling output65.2.2 ≤ 126) && (decide (ceiling output66.2.2 ≤ 126) && (decide (ceiling output67.2.2 ≤ 126) && (decide (ceiling output68.2.2 ≤ 126) && (decide (ceiling output69.2.2 ≤ 126) && (decide (ceiling output70.2.2 ≤ 126) && (decide (ceiling output71.2.2 ≤ 126) && (decide (ceiling output72.2.2 ≤ 126) && (decide (ceiling output73.2.2 ≤ 126) && (decide (ceiling output74.2.2 ≤ 126) && (decide (ceiling output75.2.2 ≤ 126) && (decide (ceiling output76.2.2 ≤ 126) && (decide (ceiling output77.2.2 ≤ 126) && (decide (ceiling output78.2.2 ≤ 126) && (decide (ceiling output79.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling64, ceiling65, ceiling66, ceiling67, ceiling68, ceiling69, ceiling70, ceiling71, ceiling72, ceiling73, ceiling74, ceiling75, ceiling76, ceiling77, ceiling78, ceiling79, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk4Safe
