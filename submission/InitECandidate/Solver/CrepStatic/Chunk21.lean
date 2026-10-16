import InitECandidate.Solver.CrepStatic.Procedure336
import InitECandidate.Solver.CrepStatic.Procedure337
import InitECandidate.Solver.CrepStatic.Procedure338
import InitECandidate.Solver.CrepStatic.Procedure339
import InitECandidate.Solver.CrepStatic.Procedure340
import InitECandidate.Solver.CrepStatic.Procedure341
import InitECandidate.Solver.CrepStatic.Procedure342
import InitECandidate.Solver.CrepStatic.Procedure343
import InitECandidate.Solver.CrepStatic.Procedure344
import InitECandidate.Solver.CrepStatic.Procedure345
import InitECandidate.Solver.CrepStatic.Procedure346
import InitECandidate.Solver.CrepStatic.Procedure347
import InitECandidate.Solver.CrepStatic.Procedure348
import InitECandidate.Solver.CrepStatic.Procedure349
import InitECandidate.Solver.CrepStatic.Procedure350
import InitECandidate.Solver.CrepStatic.Procedure351
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk21 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output336, output337, output338, output339, output340, output341, output342, output343, output344, output345, output346, output347, output348, output349, output350, output351]

theorem chunk21Safe : entriesSafe 126 chunk21 = true := by
  change (decide (ceiling output336.2.2 ≤ 126) && (decide (ceiling output337.2.2 ≤ 126) && (decide (ceiling output338.2.2 ≤ 126) && (decide (ceiling output339.2.2 ≤ 126) && (decide (ceiling output340.2.2 ≤ 126) && (decide (ceiling output341.2.2 ≤ 126) && (decide (ceiling output342.2.2 ≤ 126) && (decide (ceiling output343.2.2 ≤ 126) && (decide (ceiling output344.2.2 ≤ 126) && (decide (ceiling output345.2.2 ≤ 126) && (decide (ceiling output346.2.2 ≤ 126) && (decide (ceiling output347.2.2 ≤ 126) && (decide (ceiling output348.2.2 ≤ 126) && (decide (ceiling output349.2.2 ≤ 126) && (decide (ceiling output350.2.2 ≤ 126) && (decide (ceiling output351.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling336, ceiling337, ceiling338, ceiling339, ceiling340, ceiling341, ceiling342, ceiling343, ceiling344, ceiling345, ceiling346, ceiling347, ceiling348, ceiling349, ceiling350, ceiling351, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk21Safe
