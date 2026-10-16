import InitECandidate.Solver.WordToStackBound.Cost
import InitECandidate.Proofs.StackAnalysis.Data66
import InitECandidate.Proofs.StackAnalysis.Data713

namespace InitECandidate.Solver.WordToStackBound
open Flapjack InitECandidate.Proofs.StackAnalysis
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem ceiling66 : ceiling optimized66.2.2 ≤ 4 := by decide
theorem noInstall66 : noInstallSubprogsHOL optimized66.2.2 = true := by decide

theorem ceiling713 : ceiling optimized713.2.2 ≤ 4 := by decide
theorem noInstall713 : noInstallSubprogsHOL optimized713.2.2 = true := by decide

theorem cost66 : cost optimized66.2.2 ≤ 4 := (cost_le_ceiling _).trans ceiling66
theorem cost713 : cost optimized713.2.2 ≤ 4 := (cost_le_ceiling _).trans ceiling713

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.ceiling66
#print axioms InitECandidate.Solver.WordToStackBound.noInstall66
#print axioms InitECandidate.Solver.WordToStackBound.ceiling713
#print axioms InitECandidate.Solver.WordToStackBound.noInstall713
#print axioms InitECandidate.Solver.WordToStackBound.cost66
#print axioms InitECandidate.Solver.WordToStackBound.cost713
