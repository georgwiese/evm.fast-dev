import InitECandidate.Solver.MutableTable.MemoryModel
import InitECandidate.Solver.MutableTable.GrowRuntime.Reads

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact NaturalLayout

/-- Actual binary occupancy and distinct in-range dense slots derive the
natural count bound; it need not be postulated separately at growth. -/
theorem Occupied.length_le (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (occupied : Occupied source kind plan slots) : slots.length ≤ plan.capacity := by
  have subset : slots ⊆ List.range plan.capacity := by
    intro slot member
    exact List.mem_range.mpr (occupied.inside slot member)
  simpa only [List.length_range] using occupied.distinct.length_le_of_subset subset

/-- Doubling a reachable power-of-two capacity preserves the checked probe
power and admits the word-multiple clearing path. Range follows from actual
owned array extents, with the original minimum capacity four explicit. -/
theorem growth_shape (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (bits : Nat)
    (power : plan.capacity = 2 ^ bits) (minimum : 2 ≤ bits) :
    bits + 1 < 64 ∧ 2 * plan.capacity = 2 ^ (bits + 1) ∧ (2 * plan.capacity) % 8 = 0 := by
  have capHigh := GrowRuntime.capacity_signed_small kind plan valid
  have small : bits < 63 := by
    by_contra high
    have compare := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (show 63 ≤ bits from by omega)
    rw [← power] at compare
    omega
  have doubled : 2 * plan.capacity = 2 ^ (bits + 1) := by rw [power, Nat.pow_succ, Nat.mul_comm]
  have divide : 8 ∣ 2 ^ (bits + 1) := by
    have split : bits + 1 = 3 + (bits - 2) := by omega
    rw [split, Nat.pow_add]
    exact dvd_mul_right 8 (2 ^ (bits - 2))
  exact ⟨by omega, doubled, by rw [doubled]; exact Nat.mod_eq_zero_of_dvd divide⟩

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Occupied.length_le
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.growth_shape
