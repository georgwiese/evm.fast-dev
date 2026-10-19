import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Program
import InitECandidate.Solver.GasBudget.MemoryExpansionTransition

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Input.RlpWrite

theorem transition (s1 n1 s2 n2 : U256Value.Words) (current : BitVec 64) (aligned : current.toNat % 32 = 0)
    (finite : (resultPair s1 n1 s2 n2 current).1 ≠ 18446744073709551615#64) :
    let result := resultPair s1 n1 s2 n2 current
    let next := current + result.2
    current ≤ next ∧ next.toNat % 32 = 0 ∧
      result.1 = MemoryGasCost.resultWord next - MemoryGasCost.resultWord current ∧ result.2 = next - current := by
  let a := MemoryExpansionCost.resultPair s1 n1 current
  let middle := current + a.2
  let b := MemoryExpansionCost.resultPair s2 n2 middle
  let last := middle + b.2
  have aFinite : a.1 ≠ 18446744073709551615#64 := by
    intro equal
    apply finite
    change (if a.1 = 18446744073709551615#64 then a else merge a b).1 = _
    rw [if_pos equal]
    exact equal
  have unfolded : resultPair s1 n1 s2 n2 current = merge a b := by
    change (if a.1 = 18446744073709551615#64 then a else merge a b) = _
    rw [if_neg aFinite]
  have bFinite : b.1 ≠ 18446744073709551615#64 := by
    intro equal
    apply finite
    rw [unfolded, merge, if_pos equal]
    exact equal
  have resultEq : resultPair s1 n1 s2 n2 current = (a.1 + b.1, a.2 + b.2) := by rw [unfolded, merge, if_neg bFinite]
  obtain ⟨aOrder, aAligned, aCost, aExpand⟩ := MemoryExpansionCost.transition s1 n1 current aligned aFinite
  change current ≤ middle at aOrder
  change middle.toNat % 32 = 0 at aAligned
  change a.1 = MemoryGasCost.resultWord middle - MemoryGasCost.resultWord current at aCost
  obtain ⟨bOrder, bAligned, bCost, bExpand⟩ := MemoryExpansionCost.transition s2 n2 middle aAligned bFinite
  change middle ≤ last at bOrder
  change last.toNat % 32 = 0 at bAligned
  change b.1 = MemoryGasCost.resultWord last - MemoryGasCost.resultWord middle at bCost
  have nextWord : current + (a.2 + b.2) = last := (BitVec.add_assoc current a.2 b.2).symm
  have expandWord : a.2 + b.2 = last - current := by
    apply (BitVec.add_right_inj current).mp
    rw [nextWord, BitVec.add_comm current (last - current), BitVec.sub_add_cancel]
  have firstCost : a.1 + MemoryGasCost.resultWord current = MemoryGasCost.resultWord middle := by rw [aCost, BitVec.sub_add_cancel]
  have secondCost : b.1 + MemoryGasCost.resultWord middle = MemoryGasCost.resultWord last := by rw [bCost, BitVec.sub_add_cancel]
  have sumCost : MemoryGasCost.resultWord current + (a.1 + b.1) = MemoryGasCost.resultWord last := by
    rw [← BitVec.add_assoc, BitVec.add_comm (MemoryGasCost.resultWord current) a.1, firstCost,
      BitVec.add_comm (MemoryGasCost.resultWord middle) b.1, secondCost]
  have costWord : a.1 + b.1 = MemoryGasCost.resultWord last - MemoryGasCost.resultWord current := by
    apply (BitVec.add_right_inj (MemoryGasCost.resultWord current)).mp
    rw [sumCost, BitVec.add_comm (MemoryGasCost.resultWord current) (MemoryGasCost.resultWord last - MemoryGasCost.resultWord current), BitVec.sub_add_cancel]
  dsimp only
  rw [resultEq]
  simp only [nextWord]
  refine ⟨?_, bAligned, costWord, expandWord⟩
  apply BitVec.le_def.mpr
  have first := BitVec.le_def.mp aOrder
  have second := BitVec.le_def.mp bOrder
  omega

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.transition
