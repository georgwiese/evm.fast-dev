import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Transition
import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Value

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Input.RlpWrite

theorem affordable (s1 n1 s2 n2 : U256Value.Words) (current amount : BitVec 64) (used gas : Nat)
    (aligned : current.toNat % 32 = 0) (covered : (MemoryGasCost.resultWord current).toNat ≤ used)
    (pool : used + gas ≤ 16777216) (funded : amount.toNat ≤ gas)
    (covers : (resultPair s1 n1 s2 n2 current).1.toNat ≤ amount.toNat) :
    MemoryExpansionCost.Advance current (resultPair s1 n1 s2 n2 current).2 amount used := by
  have finite : (resultPair s1 n1 s2 n2 current).1 ≠ 18446744073709551615#64 := by
    intro equal
    have number := congrArg BitVec.toNat equal
    change (resultPair s1 n1 s2 n2 current).1.toNat = 18446744073709551615 at number
    omega
  let next := current + (resultPair s1 n1 s2 n2 current).2
  obtain ⟨order, nextAligned, costWord, expandWord⟩ := transition s1 n1 s2 n2 current aligned finite
  change current ≤ next at order
  change next.toNat % 32 = 0 at nextAligned
  change (resultPair s1 n1 s2 n2 current).1 = MemoryGasCost.resultWord next - MemoryGasCost.resultWord current at costWord
  change (resultPair s1 n1 s2 n2 current).2 = next - current at expandWord
  obtain ⟨nextCovered, costOrder, exactCost⟩ := MemoryGasCost.charge_covers (MemoryGasCost.resultWord current) (MemoryGasCost.resultWord next) amount used gas
    covered pool funded (by rw [← costWord]; exact covers)
  have exactExpand : (resultPair s1 n1 s2 n2 current).2.toNat = next.toNat - current.toNat := by rw [expandWord, BitVec.toNat_sub_of_le order]
  have orderNumber := BitVec.le_def.mp order
  have bytes := MemoryGasCost.byte_bound next (by omega)
  refine ⟨?_, nextCovered, nextAligned, ?_⟩
  · change next.toNat = current.toNat + (resultPair s1 n1 s2 n2 current).2.toNat
    omega
  · change next.toNat ≤ 178956960
    omega

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.affordable
