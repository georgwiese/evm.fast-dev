import InitECandidate.Solver.CrepStatic.Procedure128
import InitECandidate.Solver.CrepStatic.Procedure129
import InitECandidate.Solver.CrepStatic.Procedure130
import InitECandidate.Solver.CrepStatic.Procedure131
import InitECandidate.Solver.CrepStatic.Procedure132
import InitECandidate.Solver.CrepStatic.Procedure133
import InitECandidate.Solver.CrepStatic.Procedure134
import InitECandidate.Solver.CrepStatic.Procedure135
import InitECandidate.Solver.CrepStatic.Procedure136
import InitECandidate.Solver.CrepStatic.Procedure137
import InitECandidate.Solver.CrepStatic.Procedure138
import InitECandidate.Solver.CrepStatic.Procedure139
import InitECandidate.Solver.CrepStatic.Procedure140
import InitECandidate.Solver.CrepStatic.Procedure141
import InitECandidate.Solver.CrepStatic.Procedure142
import InitECandidate.Solver.CrepStatic.Procedure143
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk8 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output128, output129, output130, output131, output132, output133, output134, output135, output136, output137, output138, output139, output140, output141, output142, output143]

theorem chunk8Safe : entriesSafe 126 chunk8 = true := by
  change (decide (ceiling output128.2.2 ≤ 126) && (decide (ceiling output129.2.2 ≤ 126) && (decide (ceiling output130.2.2 ≤ 126) && (decide (ceiling output131.2.2 ≤ 126) && (decide (ceiling output132.2.2 ≤ 126) && (decide (ceiling output133.2.2 ≤ 126) && (decide (ceiling output134.2.2 ≤ 126) && (decide (ceiling output135.2.2 ≤ 126) && (decide (ceiling output136.2.2 ≤ 126) && (decide (ceiling output137.2.2 ≤ 126) && (decide (ceiling output138.2.2 ≤ 126) && (decide (ceiling output139.2.2 ≤ 126) && (decide (ceiling output140.2.2 ≤ 126) && (decide (ceiling output141.2.2 ≤ 126) && (decide (ceiling output142.2.2 ≤ 126) && (decide (ceiling output143.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling128, ceiling129, ceiling130, ceiling131, ceiling132, ceiling133, ceiling134, ceiling135, ceiling136, ceiling137, ceiling138, ceiling139, ceiling140, ceiling141, ceiling142, ceiling143, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk8Safe
