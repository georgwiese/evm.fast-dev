import InitECandidate.Solver.CrepStatic.Procedure32
import InitECandidate.Solver.CrepStatic.Procedure33
import InitECandidate.Solver.CrepStatic.Procedure34
import InitECandidate.Solver.CrepStatic.Procedure35
import InitECandidate.Solver.CrepStatic.Procedure36
import InitECandidate.Solver.CrepStatic.Procedure37
import InitECandidate.Solver.CrepStatic.Procedure38
import InitECandidate.Solver.CrepStatic.Procedure39
import InitECandidate.Solver.CrepStatic.Procedure40
import InitECandidate.Solver.CrepStatic.Procedure41
import InitECandidate.Solver.CrepStatic.Procedure42
import InitECandidate.Solver.CrepStatic.Procedure43
import InitECandidate.Solver.CrepStatic.Procedure44
import InitECandidate.Solver.CrepStatic.Procedure45
import InitECandidate.Solver.CrepStatic.Procedure46
import InitECandidate.Solver.CrepStatic.Procedure47
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk2 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output32, output33, output34, output35, output36, output37, output38, output39, output40, output41, output42, output43, output44, output45, output46, output47]

theorem chunk2Safe : entriesSafe 126 chunk2 = true := by
  change (decide (ceiling output32.2.2 ≤ 126) && (decide (ceiling output33.2.2 ≤ 126) && (decide (ceiling output34.2.2 ≤ 126) && (decide (ceiling output35.2.2 ≤ 126) && (decide (ceiling output36.2.2 ≤ 126) && (decide (ceiling output37.2.2 ≤ 126) && (decide (ceiling output38.2.2 ≤ 126) && (decide (ceiling output39.2.2 ≤ 126) && (decide (ceiling output40.2.2 ≤ 126) && (decide (ceiling output41.2.2 ≤ 126) && (decide (ceiling output42.2.2 ≤ 126) && (decide (ceiling output43.2.2 ≤ 126) && (decide (ceiling output44.2.2 ≤ 126) && (decide (ceiling output45.2.2 ≤ 126) && (decide (ceiling output46.2.2 ≤ 126) && (decide (ceiling output47.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling32, ceiling33, ceiling34, ceiling35, ceiling36, ceiling37, ceiling38, ceiling39, ceiling40, ceiling41, ceiling42, ceiling43, ceiling44, ceiling45, ceiling46, ceiling47, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk2Safe
