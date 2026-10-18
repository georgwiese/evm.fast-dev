import InitECandidate.Solver.MutableTable.TruncateCall
import InitECandidate.Solver.MutableTable.WitnessBuildBudget

namespace InitECandidate.Solver.MutableTable.Truncate

/-- Summed worst-case collision allowance through a decreasing population.
The actual successful caller is charged price(D)-price(min(D,n))+1. -/
theorem price_formula (kind : KeyHash.Kind) (count : Nat) : price kind count = match kind with
    | .account => 17 * WitnessBuild.triangle count + 13 * count
    | .indexedAccount => 26 * WitnessBuild.triangle count + 21 * count
    | .word => 13 * WitnessBuild.triangle count + 11 * count
    | .storage => 25 * WitnessBuild.triangle count + 17 * count
    | .indexedStorage => 38 * WitnessBuild.triangle count + 29 * count := by
  induction count with
  | zero => cases kind <;> rfl
  | succ count ih =>
    have deleted := Delete.model_caller_positive_price kind (count + 1) (by omega)
    rw [price, ih]
    cases kind <;> dsimp only at deleted ⊢ <;> simp only [WitnessBuild.triangle, Nat.mul_add, Nat.mul_one] <;> omega

theorem price_mono (kind : KeyHash.Kind) (small large : Nat) (bounded : small ≤ large) : price kind small ≤ price kind large := by
  induction large with
  | zero =>
    have zero : small = 0 := by omega
    rw [zero]
  | succ large ih =>
    by_cases same : small = large + 1
    · rw [same]
    · have earlier := ih (by omega)
      rw [price]
      omega

/-- The checked telescoping inequality implies the familiar difference
bound, with no charge for entries that remain after rollback. -/
theorem caller_difference_bound (kind : KeyHash.Kind) (initial final paid : Nat)
    (countBound : final ≤ initial) (charged : paid + price kind final ≤ price kind initial + 1) :
    paid ≤ price kind initial - price kind final + 1 := by
  have monotone := price_mono kind final initial countBound
  omega

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.price_formula
#print axioms InitECandidate.Solver.MutableTable.Truncate.price_mono
#print axioms InitECandidate.Solver.MutableTable.Truncate.caller_difference_bound
