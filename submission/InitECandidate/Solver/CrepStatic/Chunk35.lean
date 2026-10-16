import InitECandidate.Solver.CrepStatic.Procedure560
import InitECandidate.Solver.CrepStatic.Procedure561
import InitECandidate.Solver.CrepStatic.Procedure562
import InitECandidate.Solver.CrepStatic.Procedure563
import InitECandidate.Solver.CrepStatic.Procedure564
import InitECandidate.Solver.CrepStatic.Procedure565
import InitECandidate.Solver.CrepStatic.Procedure566
import InitECandidate.Solver.CrepStatic.Procedure567
import InitECandidate.Solver.CrepStatic.Procedure568
import InitECandidate.Solver.CrepStatic.Procedure569
import InitECandidate.Solver.CrepStatic.Procedure570
import InitECandidate.Solver.CrepStatic.Procedure571
import InitECandidate.Solver.CrepStatic.Procedure572
import InitECandidate.Solver.CrepStatic.Procedure573
import InitECandidate.Solver.CrepStatic.Procedure574
import InitECandidate.Solver.CrepStatic.Procedure575
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk35 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output560, output561, output562, output563, output564, output565, output566, output567, output568, output569, output570, output571, output572, output573, output574, output575]

theorem chunk35Safe : entriesSafe 126 chunk35 = true := by
  change (decide (ceiling output560.2.2 ≤ 126) && (decide (ceiling output561.2.2 ≤ 126) && (decide (ceiling output562.2.2 ≤ 126) && (decide (ceiling output563.2.2 ≤ 126) && (decide (ceiling output564.2.2 ≤ 126) && (decide (ceiling output565.2.2 ≤ 126) && (decide (ceiling output566.2.2 ≤ 126) && (decide (ceiling output567.2.2 ≤ 126) && (decide (ceiling output568.2.2 ≤ 126) && (decide (ceiling output569.2.2 ≤ 126) && (decide (ceiling output570.2.2 ≤ 126) && (decide (ceiling output571.2.2 ≤ 126) && (decide (ceiling output572.2.2 ≤ 126) && (decide (ceiling output573.2.2 ≤ 126) && (decide (ceiling output574.2.2 ≤ 126) && (decide (ceiling output575.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling560, ceiling561, ceiling562, ceiling563, ceiling564, ceiling565, ceiling566, ceiling567, ceiling568, ceiling569, ceiling570, ceiling571, ceiling572, ceiling573, ceiling574, ceiling575, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk35Safe
