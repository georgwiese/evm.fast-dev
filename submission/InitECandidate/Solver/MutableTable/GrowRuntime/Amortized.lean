import InitECandidate.Solver.MutableTable.GrowRuntime.CallerBudget

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open WitnessRadix

def growthSlope : KeyHash.Kind → Nat
  | .account => 7 | .indexedAccount => 11 | .word => 6 | .storage => 9 | .indexedStorage => 15
def growthPotential (kind : KeyHash.Kind) (capacity : Nat) : Nat :=
  WitnessBuild.triangle (capacity / 2) / 3 + growthSlope kind * capacity

theorem capacity_shape (capacity bits : Nat) (power : capacity = 2 ^ bits) (minimum : 2 ≤ bits) :
    4 ≤ capacity ∧ capacity % 2 = 0 := by
  have factor : capacity = 2 ^ (bits - 2) * 4 := by
    rw [power, show bits = (bits - 2) + 2 from by omega, Nat.pow_add]
    rfl
  have positive : 0 < 2 ^ (bits - 2) := Nat.pow_pos (by decide)
  constructor
  · rw [factor]
    omega
  · simp [factor, Nat.mul_mod]

theorem triangle_mono (small large : Nat) (bounded : small ≤ large) : WitnessBuild.triangle small ≤ WitnessBuild.triangle large := by
  induction large with
  | zero =>
    have same : small = 0 := by omega
    rw [same]
  | succ large ih =>
    by_cases same : small = large + 1
    · rw [same]
    · have earlier := ih (by omega)
      rw [WitnessBuild.triangle]
      omega

theorem triangle_twice (count : Nat) : WitnessBuild.triangle (2 * count) = 4 * WitnessBuild.triangle count + count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [show 2 * (count + 1) = (2 * count + 1) + 1 from by omega,
      WitnessBuild.triangle, WitnessBuild.triangle, ih, WitnessBuild.triangle]
    omega

theorem clear_small (capacity : Nat) (minimum : 4 ≤ capacity) : Zero.price (2 * capacity) + 7 ≤ 2 * capacity := by
  unfold Zero.price
  omega

/-- The entire checked growth allowance is paid by a single increase of
capacity potential. Repeated mutations do not each pay a worst-case rehash.
The leading quadratic potential coefficient is 1/24 of capacity squared. -/
theorem growth_paid_by_capacity (kind : KeyHash.Kind) (capacity count : Nat)
    (minimum : 4 ≤ capacity) (even : capacity % 2 = 0) (half : 2 * count ≤ capacity) :
    price kind (2 * capacity) count + 1 + growthPotential kind capacity ≤ growthPotential kind (2 * capacity) := by
  have countHalf : count ≤ capacity / 2 := by omega
  have bounded := triangle_mono count (capacity / 2) countHalf
  have twice : 2 * (capacity / 2) = capacity := by omega
  have doubled := triangle_twice (capacity / 2)
  rw [twice] at doubled
  have quadratic : WitnessBuild.triangle (capacity / 2) + WitnessBuild.triangle (capacity / 2) / 3 ≤ WitnessBuild.triangle capacity / 3 := by
    rw [doubled]
    omega
  have clearing := clear_small capacity minimum
  rw [caller_price]
  unfold growthPotential
  rw [show 2 * capacity / 2 = capacity from by omega]
  cases kind <;> dsimp only [growthSlope] at * <;> omega

theorem potential_mono (kind : KeyHash.Kind) (small large : Nat) (bounded : small ≤ large) :
    growthPotential kind small ≤ growthPotential kind large := by
  have half : small / 2 ≤ large / 2 := by omega
  have triangles := triangle_mono _ _ half
  have quotient : WitnessBuild.triangle (small / 2) / 3 ≤ WitnessBuild.triangle (large / 2) / 3 := by omega
  have linear := Nat.mul_le_mul_left (growthSlope kind) bounded
  unfold growthPotential
  omega

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.triangle_mono
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.capacity_shape
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.triangle_twice
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.clear_small
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.growth_paid_by_capacity
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.potential_mono
