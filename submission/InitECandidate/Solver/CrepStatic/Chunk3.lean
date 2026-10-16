import InitECandidate.Solver.CrepStatic.Procedure48
import InitECandidate.Solver.CrepStatic.Procedure49
import InitECandidate.Solver.CrepStatic.Procedure50
import InitECandidate.Solver.CrepStatic.Procedure51
import InitECandidate.Solver.CrepStatic.Procedure52
import InitECandidate.Solver.CrepStatic.Procedure53
import InitECandidate.Solver.CrepStatic.Procedure54
import InitECandidate.Solver.CrepStatic.Procedure55
import InitECandidate.Solver.CrepStatic.Procedure56
import InitECandidate.Solver.CrepStatic.Procedure57
import InitECandidate.Solver.CrepStatic.Procedure58
import InitECandidate.Solver.CrepStatic.Procedure59
import InitECandidate.Solver.CrepStatic.Procedure60
import InitECandidate.Solver.CrepStatic.Procedure61
import InitECandidate.Solver.CrepStatic.Procedure62
import InitECandidate.Solver.CrepStatic.Procedure63
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk3 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output48, output49, output50, output51, output52, output53, output54, output55, output56, output57, output58, output59, output60, output61, output62, output63]

theorem chunk3Safe : entriesSafe 126 chunk3 = true := by
  change (decide (ceiling output48.2.2 ≤ 126) && (decide (ceiling output49.2.2 ≤ 126) && (decide (ceiling output50.2.2 ≤ 126) && (decide (ceiling output51.2.2 ≤ 126) && (decide (ceiling output52.2.2 ≤ 126) && (decide (ceiling output53.2.2 ≤ 126) && (decide (ceiling output54.2.2 ≤ 126) && (decide (ceiling output55.2.2 ≤ 126) && (decide (ceiling output56.2.2 ≤ 126) && (decide (ceiling output57.2.2 ≤ 126) && (decide (ceiling output58.2.2 ≤ 126) && (decide (ceiling output59.2.2 ≤ 126) && (decide (ceiling output60.2.2 ≤ 126) && (decide (ceiling output61.2.2 ≤ 126) && (decide (ceiling output62.2.2 ≤ 126) && (decide (ceiling output63.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling48, ceiling49, ceiling50, ceiling51, ceiling52, ceiling53, ceiling54, ceiling55, ceiling56, ceiling57, ceiling58, ceiling59, ceiling60, ceiling61, ceiling62, ceiling63, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk3Safe
