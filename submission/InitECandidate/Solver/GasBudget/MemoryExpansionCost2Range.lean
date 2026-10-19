import InitECandidate.Solver.GasBudget.MemoryExpansionFiniteRange
import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Affordable

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Input.RlpWrite

/-- Both nonempty source spans fit in the single final extent selected by
the original sequential two-range calculation. -/
theorem ranges (s1 n1 s2 n2 : U256Value.Words) (current : BitVec 64)
    (aligned : current.toNat % 32 = 0)
    (finite : (resultPair s1 n1 s2 n2 current).1 ≠ 18446744073709551615#64) :
    let next := current + (resultPair s1 n1 s2 n2 current).2
    (U256Zero.resultWord n1 = 0#64 → (SatWord.resultWord s1).toNat + (SatWord.resultWord n1).toNat ≤ next.toNat) ∧
    (U256Zero.resultWord n2 = 0#64 → (SatWord.resultWord s2).toNat + (SatWord.resultWord n2).toNat ≤ next.toNat) := by
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
  have nextWord : current + (a.2 + b.2) = last := (BitVec.add_assoc current a.2 b.2).symm
  obtain ⟨aOrder, aAligned, aCost, aExpand⟩ := MemoryExpansionCost.transition s1 n1 current aligned aFinite
  change middle.toNat % 32 = 0 at aAligned
  obtain ⟨bOrder, bAligned, bCost, bExpand⟩ := MemoryExpansionCost.transition s2 n2 middle aAligned bFinite
  change middle ≤ last at bOrder
  dsimp only
  rw [resultEq]
  simp only [nextWord]
  constructor
  · intro nonempty
    have first := MemoryExpansionCost.range_of_finite s1 n1 current aligned nonempty aFinite
    change (SatWord.resultWord s1).toNat + (SatWord.resultWord n1).toNat ≤ middle.toNat at first
    exact first.trans (BitVec.le_def.mp bOrder)
  · intro nonempty
    exact MemoryExpansionCost.range_of_finite s2 n2 middle aAligned nonempty bFinite

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.ranges
