import InitECandidate.Solver.CrepStatic.Procedure768
import InitECandidate.Solver.CrepStatic.Procedure769
import InitECandidate.Solver.CrepStatic.Procedure770
import InitECandidate.Solver.CrepStatic.Procedure771
import InitECandidate.Solver.CrepStatic.Procedure772
import InitECandidate.Solver.CrepStatic.Procedure773
import InitECandidate.Solver.CrepStatic.Procedure774
import InitECandidate.Solver.CrepStatic.Procedure775
import InitECandidate.Solver.CrepStatic.Procedure776
import InitECandidate.Solver.CrepStatic.Procedure777
import InitECandidate.Solver.CrepStatic.Procedure778
import InitECandidate.Solver.CrepStatic.Procedure779
import InitECandidate.Solver.CrepStatic.Procedure780
import InitECandidate.Solver.CrepStatic.Procedure781
import InitECandidate.Solver.CrepStatic.Procedure782
import InitECandidate.Solver.CrepStatic.Procedure783
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk48 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output768, output769, output770, output771, output772, output773, output774, output775, output776, output777, output778, output779, output780, output781, output782, output783]

theorem chunk48Safe : entriesSafe 126 chunk48 = true := by
  change (decide (ceiling output768.2.2 ≤ 126) && (decide (ceiling output769.2.2 ≤ 126) && (decide (ceiling output770.2.2 ≤ 126) && (decide (ceiling output771.2.2 ≤ 126) && (decide (ceiling output772.2.2 ≤ 126) && (decide (ceiling output773.2.2 ≤ 126) && (decide (ceiling output774.2.2 ≤ 126) && (decide (ceiling output775.2.2 ≤ 126) && (decide (ceiling output776.2.2 ≤ 126) && (decide (ceiling output777.2.2 ≤ 126) && (decide (ceiling output778.2.2 ≤ 126) && (decide (ceiling output779.2.2 ≤ 126) && (decide (ceiling output780.2.2 ≤ 126) && (decide (ceiling output781.2.2 ≤ 126) && (decide (ceiling output782.2.2 ≤ 126) && (decide (ceiling output783.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling768, ceiling769, ceiling770, ceiling771, ceiling772, ceiling773, ceiling774, ceiling775, ceiling776, ceiling777, ceiling778, ceiling779, ceiling780, ceiling781, ceiling782, ceiling783, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk48Safe
