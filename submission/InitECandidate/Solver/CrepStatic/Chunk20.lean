import InitECandidate.Solver.CrepStatic.Procedure320
import InitECandidate.Solver.CrepStatic.Procedure321
import InitECandidate.Solver.CrepStatic.Procedure322
import InitECandidate.Solver.CrepStatic.Procedure323
import InitECandidate.Solver.CrepStatic.Procedure324
import InitECandidate.Solver.CrepStatic.Procedure325
import InitECandidate.Solver.CrepStatic.Procedure326
import InitECandidate.Solver.CrepStatic.Procedure327
import InitECandidate.Solver.CrepStatic.Procedure328
import InitECandidate.Solver.CrepStatic.Procedure329
import InitECandidate.Solver.CrepStatic.Procedure330
import InitECandidate.Solver.CrepStatic.Procedure331
import InitECandidate.Solver.CrepStatic.Procedure332
import InitECandidate.Solver.CrepStatic.Procedure333
import InitECandidate.Solver.CrepStatic.Procedure334
import InitECandidate.Solver.CrepStatic.Procedure335
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk20 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output320, output321, output322, output323, output324, output325, output326, output327, output328, output329, output330, output331, output332, output333, output334, output335]

theorem chunk20Safe : entriesSafe 126 chunk20 = true := by
  change (decide (ceiling output320.2.2 ≤ 126) && (decide (ceiling output321.2.2 ≤ 126) && (decide (ceiling output322.2.2 ≤ 126) && (decide (ceiling output323.2.2 ≤ 126) && (decide (ceiling output324.2.2 ≤ 126) && (decide (ceiling output325.2.2 ≤ 126) && (decide (ceiling output326.2.2 ≤ 126) && (decide (ceiling output327.2.2 ≤ 126) && (decide (ceiling output328.2.2 ≤ 126) && (decide (ceiling output329.2.2 ≤ 126) && (decide (ceiling output330.2.2 ≤ 126) && (decide (ceiling output331.2.2 ≤ 126) && (decide (ceiling output332.2.2 ≤ 126) && (decide (ceiling output333.2.2 ≤ 126) && (decide (ceiling output334.2.2 ≤ 126) && (decide (ceiling output335.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling320, ceiling321, ceiling322, ceiling323, ceiling324, ceiling325, ceiling326, ceiling327, ceiling328, ceiling329, ceiling330, ceiling331, ceiling332, ceiling333, ceiling334, ceiling335, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk20Safe
