import InitECandidate.Solver.CrepStatic.Procedure352
import InitECandidate.Solver.CrepStatic.Procedure353
import InitECandidate.Solver.CrepStatic.Procedure354
import InitECandidate.Solver.CrepStatic.Procedure355
import InitECandidate.Solver.CrepStatic.Procedure356
import InitECandidate.Solver.CrepStatic.Procedure357
import InitECandidate.Solver.CrepStatic.Procedure358
import InitECandidate.Solver.CrepStatic.Procedure359
import InitECandidate.Solver.CrepStatic.Procedure360
import InitECandidate.Solver.CrepStatic.Procedure361
import InitECandidate.Solver.CrepStatic.Procedure362
import InitECandidate.Solver.CrepStatic.Procedure363
import InitECandidate.Solver.CrepStatic.Procedure364
import InitECandidate.Solver.CrepStatic.Procedure365
import InitECandidate.Solver.CrepStatic.Procedure366
import InitECandidate.Solver.CrepStatic.Procedure367
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk22 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output352, output353, output354, output355, output356, output357, output358, output359, output360, output361, output362, output363, output364, output365, output366, output367]

theorem chunk22Safe : entriesSafe 126 chunk22 = true := by
  change (decide (ceiling output352.2.2 ≤ 126) && (decide (ceiling output353.2.2 ≤ 126) && (decide (ceiling output354.2.2 ≤ 126) && (decide (ceiling output355.2.2 ≤ 126) && (decide (ceiling output356.2.2 ≤ 126) && (decide (ceiling output357.2.2 ≤ 126) && (decide (ceiling output358.2.2 ≤ 126) && (decide (ceiling output359.2.2 ≤ 126) && (decide (ceiling output360.2.2 ≤ 126) && (decide (ceiling output361.2.2 ≤ 126) && (decide (ceiling output362.2.2 ≤ 126) && (decide (ceiling output363.2.2 ≤ 126) && (decide (ceiling output364.2.2 ≤ 126) && (decide (ceiling output365.2.2 ≤ 126) && (decide (ceiling output366.2.2 ≤ 126) && (decide (ceiling output367.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling352, ceiling353, ceiling354, ceiling355, ceiling356, ceiling357, ceiling358, ceiling359, ceiling360, ceiling361, ceiling362, ceiling363, ceiling364, ceiling365, ceiling366, ceiling367, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk22Safe
