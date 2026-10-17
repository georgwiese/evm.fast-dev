import InitECandidate.Solver.MutableTable.SetModelCall
import InitECandidate.Solver.MutableTable.GrowRuntime.CallerBudget
import InitECandidate.Solver.MutableTable.SetNoGrowthBudget

namespace InitECandidate.Solver.MutableTable.Set
open WitnessRadix

/-- A possible growth adds exactly its separate checked caller allowance to
the existing setter allowance. The refined caller contract charges only the
smaller allowance when the actual returned layout stays unchanged. -/
theorem model_caller_decompose (kind : KeyHash.Kind) (capacity count : Nat) :
    modelPrice kind capacity count + 1 = noGrowthPrice kind count + 1 + (GrowRuntime.price kind (2 * capacity) count + 1) := by
  dsimp only [modelPrice, afterGrowPrice, noGrowthPrice, Insert.rawPrice]
  omega

theorem model_caller_price (kind : KeyHash.Kind) (capacity count : Nat) :
    modelPrice kind capacity count + 1 = Zero.price (2 * capacity) + WitnessBuild.triangle count +
      match kind with
      | .account => 19 * count + 19
      | .indexedAccount => 28 * count + 34
      | .word => 15 * count + 17
      | .storage => 27 * count + 23
      | .indexedStorage => 40 * count + 46 := by
  rw [model_caller_decompose, no_growth_caller_price, GrowRuntime.caller_price]
  cases kind <;> dsimp only <;> omega

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.model_caller_decompose
#print axioms InitECandidate.Solver.MutableTable.Set.model_caller_price
