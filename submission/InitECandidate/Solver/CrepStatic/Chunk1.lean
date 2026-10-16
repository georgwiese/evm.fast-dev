import InitECandidate.Solver.CrepStatic.Procedure16
import InitECandidate.Solver.CrepStatic.Procedure17
import InitECandidate.Solver.CrepStatic.Procedure18
import InitECandidate.Solver.CrepStatic.Procedure19
import InitECandidate.Solver.CrepStatic.Procedure20
import InitECandidate.Solver.CrepStatic.Procedure21
import InitECandidate.Solver.CrepStatic.Procedure22
import InitECandidate.Solver.CrepStatic.Procedure23
import InitECandidate.Solver.CrepStatic.Procedure24
import InitECandidate.Solver.CrepStatic.Procedure25
import InitECandidate.Solver.CrepStatic.Procedure26
import InitECandidate.Solver.CrepStatic.Procedure27
import InitECandidate.Solver.CrepStatic.Procedure28
import InitECandidate.Solver.CrepStatic.Procedure29
import InitECandidate.Solver.CrepStatic.Procedure30
import InitECandidate.Solver.CrepStatic.Procedure31
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk1 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [output16, output17, output18, output19, output20, output21, output22, output23, output24, output25, output26, output27, output28, output29, output30, output31]

theorem chunk1Safe : entriesSafe 126 chunk1 = true := by
  change (decide (ceiling output16.2.2 ≤ 126) && (decide (ceiling output17.2.2 ≤ 126) && (decide (ceiling output18.2.2 ≤ 126) && (decide (ceiling output19.2.2 ≤ 126) && (decide (ceiling output20.2.2 ≤ 126) && (decide (ceiling output21.2.2 ≤ 126) && (decide (ceiling output22.2.2 ≤ 126) && (decide (ceiling output23.2.2 ≤ 126) && (decide (ceiling output24.2.2 ≤ 126) && (decide (ceiling output25.2.2 ≤ 126) && (decide (ceiling output26.2.2 ≤ 126) && (decide (ceiling output27.2.2 ≤ 126) && (decide (ceiling output28.2.2 ≤ 126) && (decide (ceiling output29.2.2 ≤ 126) && (decide (ceiling output30.2.2 ≤ 126) && (decide (ceiling output31.2.2 ≤ 126) && true)))))))))))))))) = true
  simp only [ceiling16, ceiling17, ceiling18, ceiling19, ceiling20, ceiling21, ceiling22, ceiling23, ceiling24, ceiling25, ceiling26, ceiling27, ceiling28, ceiling29, ceiling30, ceiling31, decide_true, Bool.true_and]

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.chunk1Safe
