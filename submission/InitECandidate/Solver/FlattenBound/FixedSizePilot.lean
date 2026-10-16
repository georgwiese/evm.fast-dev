import InitECandidate.Solver.FlattenBound.Common
import InitECandidate.Proofs.BackendStages.Named713

namespace InitECandidate.Solver.FlattenBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- This fixed straight-line initialization body controls any uniform
whole-code syntax ceiling. It must not be charged on every unrelated call. -/
theorem named713_nodes : nodes InitECandidate.Proofs.BackendStages.Named713.2 = 12091 := by
  decide

theorem named713_uniform_limit (limit : Nat)
    (bounded : nodes InitECandidate.Proofs.BackendStages.Named713.2 ≤ limit) :
    12091 ≤ limit := by simpa only [named713_nodes] using bounded

end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.named713_nodes
#print axioms InitECandidate.Solver.FlattenBound.named713_uniform_limit
