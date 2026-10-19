import InitECandidate.Solver.GasBudget.MemoryExpansionCostAffordable

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Input.RlpWrite

/-- A nonsentinel cost for a nonempty access places the entire actual
saturated span within the selected next length. -/
theorem range_of_finite (start size : U256Value.Words) (current : BitVec 64)
    (aligned : current.toNat % 32 = 0) (nonempty : U256Zero.resultWord size = 0#64)
    (finite : (resultPair start size current).1 ≠ 18446744073709551615#64) :
    (SatWord.resultWord start).toNat + (SatWord.resultWord size).toNat ≤
      (current + (resultPair start size current).2).toNat := by
  let endpoint := SaturatingAdd.resultWord (SatWord.resultWord start) (SatWord.resultWord size)
  have result : resultPair start size current = endPair current endpoint := by simp [resultPair, nonempty, endpoint]
  have notMaximum : endpoint ≠ 18446744073709551615#64 := by
    intro equal
    have maxPair : resultPair start size current = (18446744073709551615#64, 0#64) := by rw [result, endPair, if_pos equal]
    exact finite (congrArg Prod.fst maxPair)
  have endpointSmall : endpoint.toNat < 18446744073709551615 := by
    have bound := endpoint.isLt
    have different : endpoint.toNat ≠ 18446744073709551615 := by
      intro equal
      apply notMaximum
      apply BitVec.eq_of_toNat_eq
      exact equal
    omega
  have natural : endpoint.toNat = (SatWord.resultWord start).toNat + (SatWord.resultWord size).toNat := by
    have number := SaturatingAdd.result_nat (SatWord.resultWord start) (SatWord.resultWord size)
    change endpoint.toNat = min (2 ^ 64 - 1) _ at number
    omega
  have roundedAbove := Ceil32.ge_self endpoint
  change endpoint.toNat ≤ (Ceil32.resultWord endpoint).toNat at roundedAbove
  rw [result, endPair, if_neg notMaximum, Ceil32.fixed_of_aligned current aligned] at finite ⊢
  by_cases fits : Ceil32.resultWord endpoint ≤ current
  · rw [if_pos fits]
    have order := BitVec.le_def.mp fits
    simp only [BitVec.add_zero]
    omega
  · rw [if_neg fits] at finite ⊢
    by_cases maxCost : MemoryGasCost.resultWord (Ceil32.resultWord endpoint) = 18446744073709551615#64
    · rw [finalPair, if_pos maxCost] at finite
      exact (finite rfl).elim
    · rw [finalPair, if_neg maxCost]
      have next : current + (Ceil32.resultWord endpoint - current) = Ceil32.resultWord endpoint := by
        rw [BitVec.add_comm]
        exact BitVec.sub_add_cancel _ _
      change _ ≤ (current + (Ceil32.resultWord endpoint - current)).toNat
      rw [next, ← natural]
      exact roundedAbove

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.range_of_finite
