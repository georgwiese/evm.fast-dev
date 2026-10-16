import InitECandidate.Solver.CrepStatic.Procedure400
import InitECandidate.Solver.CrepStatic.Procedure401
import InitECandidate.Solver.CrepStatic.Procedure402
import InitECandidate.Solver.CrepStatic.Procedure403
import InitECandidate.Solver.CrepStatic.Procedure404
import InitECandidate.Solver.CrepStatic.Procedure405
import InitECandidate.Solver.CrepStatic.Procedure406
import InitECandidate.Solver.CrepStatic.Procedure407
import InitECandidate.Solver.CrepStatic.Procedure408
import InitECandidate.Solver.CrepStatic.Procedure409
import InitECandidate.Solver.CrepStatic.Procedure410
import InitECandidate.Solver.CrepStatic.Procedure411
import InitECandidate.Solver.CrepStatic.Procedure412
import InitECandidate.Solver.CrepStatic.Procedure413
import InitECandidate.Solver.CrepStatic.Procedure414
import InitECandidate.Solver.CrepStatic.Procedure415
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk25 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output400, output401, output402, output403, output404, output405, output406, output407, output408, output409, output410, output411, output412, output413, output414, output415]

theorem chunk25Safe : entriesSafe 126 chunk25 = true := by
  change (decide (ceiling output400.2.2 ≤ 126) && (decide (ceiling output401.2.2 ≤ 126) && (decide (ceiling output402.2.2 ≤ 126) && (decide (ceiling output403.2.2 ≤ 126) && (decide (ceiling output404.2.2 ≤ 126) && (decide (ceiling output405.2.2 ≤ 126) && (decide (ceiling output406.2.2 ≤ 126) && (decide (ceiling output407.2.2 ≤ 126) && (decide (ceiling output408.2.2 ≤ 126) && (decide (ceiling output409.2.2 ≤ 126) && (decide (ceiling output410.2.2 ≤ 126) && (decide (ceiling output411.2.2 ≤ 126) && (decide (ceiling output412.2.2 ≤ 126) && (decide (ceiling output413.2.2 ≤ 126) && (decide (ceiling output414.2.2 ≤ 126) && (decide (ceiling output415.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling400, ceiling401, ceiling402, ceiling403, ceiling404, ceiling405, ceiling406, ceiling407, ceiling408, ceiling409, ceiling410, ceiling411, ceiling412, ceiling413, ceiling414, ceiling415, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk25Safe
