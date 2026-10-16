import InitECandidate.Solver.CrepStatic.Procedure256
import InitECandidate.Solver.CrepStatic.Procedure257
import InitECandidate.Solver.CrepStatic.Procedure258
import InitECandidate.Solver.CrepStatic.Procedure259
import InitECandidate.Solver.CrepStatic.Procedure260
import InitECandidate.Solver.CrepStatic.Procedure261
import InitECandidate.Solver.CrepStatic.Procedure262
import InitECandidate.Solver.CrepStatic.Procedure263
import InitECandidate.Solver.CrepStatic.Procedure264
import InitECandidate.Solver.CrepStatic.Procedure265
import InitECandidate.Solver.CrepStatic.Procedure266
import InitECandidate.Solver.CrepStatic.Procedure267
import InitECandidate.Solver.CrepStatic.Procedure268
import InitECandidate.Solver.CrepStatic.Procedure269
import InitECandidate.Solver.CrepStatic.Procedure270
import InitECandidate.Solver.CrepStatic.Procedure271
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk16 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output256, output257, output258, output259, output260, output261, output262, output263, output264, output265, output266, output267, output268, output269, output270, output271]

theorem chunk16Safe : entriesSafe 126 chunk16 = true := by
  change (decide (ceiling output256.2.2 ≤ 126) && (decide (ceiling output257.2.2 ≤ 126) && (decide (ceiling output258.2.2 ≤ 126) && (decide (ceiling output259.2.2 ≤ 126) && (decide (ceiling output260.2.2 ≤ 126) && (decide (ceiling output261.2.2 ≤ 126) && (decide (ceiling output262.2.2 ≤ 126) && (decide (ceiling output263.2.2 ≤ 126) && (decide (ceiling output264.2.2 ≤ 126) && (decide (ceiling output265.2.2 ≤ 126) && (decide (ceiling output266.2.2 ≤ 126) && (decide (ceiling output267.2.2 ≤ 126) && (decide (ceiling output268.2.2 ≤ 126) && (decide (ceiling output269.2.2 ≤ 126) && (decide (ceiling output270.2.2 ≤ 126) && (decide (ceiling output271.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling256, ceiling257, ceiling258, ceiling259, ceiling260, ceiling261, ceiling262, ceiling263, ceiling264, ceiling265, ceiling266, ceiling267, ceiling268, ceiling269, ceiling270, ceiling271, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk16Safe
