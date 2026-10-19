import InitECandidate.Solver.GasBudget.MemoryExpansionCostAffordable

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Input.RlpWrite

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem maximum_cost : MemoryGasCost.resultWord 18446744073709551615#64 = 18446744073709551615#64 := by decide

/-- A nonsentinel result gives an aligned, nondecreasing selected length
and exact word differences, before imposing a finite gas budget. -/
theorem end_transition (current endpoint : BitVec 64) (aligned : current.toNat % 32 = 0)
    (finite : (endPair current endpoint).1 ≠ 18446744073709551615#64) :
    let result := endPair current endpoint
    let next := current + result.2
    current ≤ next ∧ next.toNat % 32 = 0 ∧
      result.1 = MemoryGasCost.resultWord next - MemoryGasCost.resultWord current ∧ result.2 = next - current := by
  have notEnd : endpoint ≠ 18446744073709551615#64 := by
    intro equal
    apply finite
    simp [endPair, equal]
  have currentFixed := Ceil32.fixed_of_aligned current aligned
  by_cases noGrowth : Ceil32.resultWord endpoint ≤ current
  · simp [endPair, notEnd, currentFixed, noGrowth, aligned]
  · have notCost : MemoryGasCost.resultWord (Ceil32.resultWord endpoint) ≠ 18446744073709551615#64 := by
      intro equal
      apply finite
      simp [endPair, notEnd, currentFixed, noGrowth, finalPair, equal]
    have notLength : Ceil32.resultWord endpoint ≠ 18446744073709551615#64 := by
      intro equal
      apply notCost
      rw [equal, maximum_cost]
    have nextAligned := Ceil32.aligned_of_not_max endpoint notLength
    dsimp only
    rw [endPair, if_neg notEnd, currentFixed, if_neg noGrowth, finalPair, if_neg notCost]
    have nextWord : current + (Ceil32.resultWord endpoint - current) = Ceil32.resultWord endpoint := by
      rw [BitVec.add_comm]
      exact BitVec.sub_add_cancel _ _
    simp only [nextWord]
    refine ⟨?_, nextAligned, by simp, by simp⟩
    apply BitVec.le_def.mpr
    have growing : current.toNat < (Ceil32.resultWord endpoint).toNat := by
      change ¬(Ceil32.resultWord endpoint).toNat ≤ current.toNat at noGrowth
      omega
    omega

theorem transition (start size : U256Value.Words) (current : BitVec 64) (aligned : current.toNat % 32 = 0)
    (finite : (resultPair start size current).1 ≠ 18446744073709551615#64) :
    let result := resultPair start size current
    let next := current + result.2
    current ≤ next ∧ next.toNat % 32 = 0 ∧
      result.1 = MemoryGasCost.resultWord next - MemoryGasCost.resultWord current ∧ result.2 = next - current := by
  by_cases empty : U256Zero.resultWord size ≠ 0#64
  · simp [resultPair, empty, aligned]
  · rw [resultPair, if_neg empty] at finite ⊢
    exact end_transition current _ aligned finite

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.maximum_cost
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.end_transition
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.transition
