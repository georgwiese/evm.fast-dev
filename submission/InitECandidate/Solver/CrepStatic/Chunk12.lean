import InitECandidate.Solver.CrepStatic.Procedure192
import InitECandidate.Solver.CrepStatic.Procedure193
import InitECandidate.Solver.CrepStatic.Procedure194
import InitECandidate.Solver.CrepStatic.Procedure195
import InitECandidate.Solver.CrepStatic.Procedure196
import InitECandidate.Solver.CrepStatic.Procedure197
import InitECandidate.Solver.CrepStatic.Procedure198
import InitECandidate.Solver.CrepStatic.Procedure199
import InitECandidate.Solver.CrepStatic.Procedure200
import InitECandidate.Solver.CrepStatic.Procedure201
import InitECandidate.Solver.CrepStatic.Procedure202
import InitECandidate.Solver.CrepStatic.Procedure203
import InitECandidate.Solver.CrepStatic.Procedure204
import InitECandidate.Solver.CrepStatic.Procedure205
import InitECandidate.Solver.CrepStatic.Procedure206
import InitECandidate.Solver.CrepStatic.Procedure207
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk12 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output192, output193, output194, output195, output196, output197, output198, output199, output200, output201, output202, output203, output204, output205, output206, output207]

theorem chunk12Safe : entriesSafe 126 chunk12 = true := by
  change (decide (ceiling output192.2.2 ≤ 126) && (decide (ceiling output193.2.2 ≤ 126) && (decide (ceiling output194.2.2 ≤ 126) && (decide (ceiling output195.2.2 ≤ 126) && (decide (ceiling output196.2.2 ≤ 126) && (decide (ceiling output197.2.2 ≤ 126) && (decide (ceiling output198.2.2 ≤ 126) && (decide (ceiling output199.2.2 ≤ 126) && (decide (ceiling output200.2.2 ≤ 126) && (decide (ceiling output201.2.2 ≤ 126) && (decide (ceiling output202.2.2 ≤ 126) && (decide (ceiling output203.2.2 ≤ 126) && (decide (ceiling output204.2.2 ≤ 126) && (decide (ceiling output205.2.2 ≤ 126) && (decide (ceiling output206.2.2 ≤ 126) && (decide (ceiling output207.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling192, ceiling193, ceiling194, ceiling195, ceiling196, ceiling197, ceiling198, ceiling199, ceiling200, ceiling201, ceiling202, ceiling203, ceiling204, ceiling205, ceiling206, ceiling207, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk12Safe
