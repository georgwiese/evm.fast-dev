import InitECandidate.Solver.CrepStatic.Procedure80
import InitECandidate.Solver.CrepStatic.Procedure81
import InitECandidate.Solver.CrepStatic.Procedure82
import InitECandidate.Solver.CrepStatic.Procedure83
import InitECandidate.Solver.CrepStatic.Procedure84
import InitECandidate.Solver.CrepStatic.Procedure85
import InitECandidate.Solver.CrepStatic.Procedure86
import InitECandidate.Solver.CrepStatic.Procedure87
import InitECandidate.Solver.CrepStatic.Procedure88
import InitECandidate.Solver.CrepStatic.Procedure89
import InitECandidate.Solver.CrepStatic.Procedure90
import InitECandidate.Solver.CrepStatic.Procedure91
import InitECandidate.Solver.CrepStatic.Procedure92
import InitECandidate.Solver.CrepStatic.Procedure93
import InitECandidate.Solver.CrepStatic.Procedure94
import InitECandidate.Solver.CrepStatic.Procedure95
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk5 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output80, output81, output82, output83, output84, output85, output86, output87, output88, output89, output90, output91, output92, output93, output94, output95]

theorem chunk5Safe : entriesSafe 126 chunk5 = true := by
  change (decide (ceiling output80.2.2 ≤ 126) && (decide (ceiling output81.2.2 ≤ 126) && (decide (ceiling output82.2.2 ≤ 126) && (decide (ceiling output83.2.2 ≤ 126) && (decide (ceiling output84.2.2 ≤ 126) && (decide (ceiling output85.2.2 ≤ 126) && (decide (ceiling output86.2.2 ≤ 126) && (decide (ceiling output87.2.2 ≤ 126) && (decide (ceiling output88.2.2 ≤ 126) && (decide (ceiling output89.2.2 ≤ 126) && (decide (ceiling output90.2.2 ≤ 126) && (decide (ceiling output91.2.2 ≤ 126) && (decide (ceiling output92.2.2 ≤ 126) && (decide (ceiling output93.2.2 ≤ 126) && (decide (ceiling output94.2.2 ≤ 126) && (decide (ceiling output95.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling80, ceiling81, ceiling82, ceiling83, ceiling84, ceiling85, ceiling86, ceiling87, ceiling88, ceiling89, ceiling90, ceiling91, ceiling92, ceiling93, ceiling94, ceiling95, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk5Safe
