import InitECandidate.Solver.GasBudget.JournalAggregatePrice

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack PanSemStateFiniteExact MutableTable

theorem triangle_square (count : Nat) :
    2 * WitnessBuild.triangle count + count = count * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [WitnessBuild.triangle, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

/-- Each individual restore is capped by the physical journal reservation.
Many separate restores therefore pay a linear allowance in their total
consumed records, even when that total exceeds the reservation capacity. -/
theorem triangle_capped (count capacity : Nat) (bounded : count ≤ capacity) :
    2 * WitnessBuild.triangle count ≤ (capacity - 1) * count := by
  have square := triangle_square count
  have product := Nat.mul_le_mul_right count bounded
  simp only [Nat.sub_mul, Nat.one_mul]
  omega

def cappedSlope (population capacity : Nat) : Nat :=
  38 * population + 40 + 19 * (capacity - 1)

theorem price_capped (population count capacity : Nat) (bounded : count ≤ capacity) :
    price population count ≤ cappedSlope population capacity * count := by
  have quadratic : 38 * WitnessBuild.triangle count ≤ (19 * (capacity - 1)) * count := by
    simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 19 (triangle_capped count capacity bounded)
  simp only [price, cappedSlope, Nat.add_mul]
  omega

theorem price_sum_capped (population capacity : Nat) (counts : List Nat)
    (bounded : ∀ count ∈ counts, count ≤ capacity) :
    (counts.map (price population)).sum ≤ cappedSlope population capacity * counts.sum := by
  induction counts with
  | nil => simp
  | cons count counts ih =>
    have first := price_capped population count capacity (bounded count (by simp))
    have rest := ih (fun n member => bounded n (by simp [member]))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

theorem accounted_capped_price {initial : Nat} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (ledger : CounterLedger initial source) (population capacity : Nat) (counts : List Nat)
    (bounded : ∀ count ∈ counts, count ≤ capacity) (actual : counts.sum = ledger.restored) :
    counts.length + (counts.map (price population)).sum ≤
      counts.length + cappedSlope population capacity * (initial + ledger.appended) := by
  have combined := price_sum_capped population capacity counts bounded
  have total := Nat.mul_le_mul_left (cappedSlope population capacity) ledger.restored_le
  rw [actual] at combined
  omega

theorem close_accounted_capped_price {ι : Type} [Fintype ι] {initial : Nat}
    {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → TableFamily.Object}
    (family : TableFamily.Model source cursor objects) (ledger : CounterLedger initial source)
    (paid other initialPotential population capacity : Nat) (counts : List Nat)
    (bounded : ∀ count ∈ counts, count ≤ capacity) (actual : counts.sum = ledger.restored)
    (amortized : paid + initialPotential ≤ other + (counts.map (price population)).sum + TableFamily.potential objects) :
    paid ≤ other + cappedSlope population capacity * (initial + ledger.appended) + 17497087144886042 := by
  have potential := family.potential_bound
  have combined := price_sum_capped population capacity counts bounded
  have total := Nat.mul_le_mul_left (cappedSlope population capacity) ledger.restored_le
  rw [actual] at combined
  omega

theorem original_capped_slope : cappedSlope 268435456 524288 = 10210508821 := by decide

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.triangle_square
#print axioms InitECandidate.Solver.GasBudget.Journal.triangle_capped
#print axioms InitECandidate.Solver.GasBudget.Journal.price_capped
#print axioms InitECandidate.Solver.GasBudget.Journal.price_sum_capped
#print axioms InitECandidate.Solver.GasBudget.Journal.accounted_capped_price
#print axioms InitECandidate.Solver.GasBudget.Journal.close_accounted_capped_price
#print axioms InitECandidate.Solver.GasBudget.Journal.original_capped_slope
