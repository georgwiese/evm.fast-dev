import InitECandidate.Solver.CrepStatic.Procedure288
import InitECandidate.Solver.CrepStatic.Procedure289
import InitECandidate.Solver.CrepStatic.Procedure290
import InitECandidate.Solver.CrepStatic.Procedure291
import InitECandidate.Solver.CrepStatic.Procedure292
import InitECandidate.Solver.CrepStatic.Procedure293
import InitECandidate.Solver.CrepStatic.Procedure294
import InitECandidate.Solver.CrepStatic.Procedure295
import InitECandidate.Solver.CrepStatic.Procedure296
import InitECandidate.Solver.CrepStatic.Procedure297
import InitECandidate.Solver.CrepStatic.Procedure298
import InitECandidate.Solver.CrepStatic.Procedure299
import InitECandidate.Solver.CrepStatic.Procedure300
import InitECandidate.Solver.CrepStatic.Procedure301
import InitECandidate.Solver.CrepStatic.Procedure302
import InitECandidate.Solver.CrepStatic.Procedure303
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk18 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output288, output289, output290, output291, output292, output293, output294, output295, output296, output297, output298, output299, output300, output301, output302, output303]

theorem chunk18Safe : entriesSafe 126 chunk18 = true := by
  change (decide (ceiling output288.2.2 ≤ 126) && (decide (ceiling output289.2.2 ≤ 126) && (decide (ceiling output290.2.2 ≤ 126) && (decide (ceiling output291.2.2 ≤ 126) && (decide (ceiling output292.2.2 ≤ 126) && (decide (ceiling output293.2.2 ≤ 126) && (decide (ceiling output294.2.2 ≤ 126) && (decide (ceiling output295.2.2 ≤ 126) && (decide (ceiling output296.2.2 ≤ 126) && (decide (ceiling output297.2.2 ≤ 126) && (decide (ceiling output298.2.2 ≤ 126) && (decide (ceiling output299.2.2 ≤ 126) && (decide (ceiling output300.2.2 ≤ 126) && (decide (ceiling output301.2.2 ≤ 126) && (decide (ceiling output302.2.2 ≤ 126) && (decide (ceiling output303.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling288, ceiling289, ceiling290, ceiling291, ceiling292, ceiling293, ceiling294, ceiling295, ceiling296, ceiling297, ceiling298, ceiling299, ceiling300, ceiling301, ceiling302, ceiling303, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk18Safe
