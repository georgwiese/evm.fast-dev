import InitECandidate.Solver.GasBudget.ForwardMemoryCredit
import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Affordable

namespace InitECandidate.Solver.GasBudget.ForwardCredit
open Flapjack Input.RlpWrite

/-- The affordable original up-front fee supplies cost2's real expansion.
After the actual stipend debit, new memory cost is still covered with100 gas
of net progress; a parent used word need not be monotone at the transfer. -/
theorem memory_advance (s1 n1 s2 n2 : U256Value.Words) (current access : BitVec 64) (words : U256Zero.Quad)
    (oldUsed gas chargedUsed forwardedUsed : Nat)
    (aligned : current.toNat % 32 = 0) (covered : (MemoryGasCost.resultWord current).toNat ≤ oldUsed)
    (pool : oldUsed + gas ≤ 16777216)
    (accessLower : 100 ≤ access.toNat) (accessUpper : access.toNat ≤ 3000)
    (affordable : (SaturatingAdd.resultWord (access + valueFee words) (MemoryExpansionCost2.resultPair s1 n1 s2 n2 current).1).toNat ≤ gas)
    (credit : oldUsed + (SaturatingAdd.resultWord (access + valueFee words) (MemoryExpansionCost2.resultPair s1 n1 s2 n2 current).1).toNat ≤ chargedUsed)
    (debit : forwardedUsed + (CallGas.stipend words).toNat = chargedUsed) :
    MemoryExpansionCost.Advance current (MemoryExpansionCost2.resultPair s1 n1 s2 n2 current).2
      (MemoryExpansionCost2.resultPair s1 n1 s2 n2 current).1 oldUsed ∧
    (MemoryGasCost.resultWord (current + (MemoryExpansionCost2.resultPair s1 n1 s2 n2 current).2)).toNat + 100 ≤ forwardedUsed := by
  let cost := (MemoryExpansionCost2.resultPair s1 n1 s2 n2 current).1
  have small : (SaturatingAdd.resultWord (access + valueFee words) cost).toNat ≤ 16777216 := by
    change (SaturatingAdd.resultWord (access + valueFee words) cost).toNat ≤ gas at affordable
    omega
  have costLower : cost.toNat ≤ (SaturatingAdd.resultWord (access + valueFee words) cost).toNat := by
    rw [SaturatingAdd.result_nat]
    have finite := cost.isLt
    omega
  have costFunded : cost.toNat ≤ gas := costLower.trans affordable
  have advance := MemoryExpansionCost2.affordable s1 n1 s2 n2 current cost oldUsed gas aligned covered pool costFunded (Nat.le_refl _)
  have remaining := after_forward oldUsed chargedUsed forwardedUsed words access cost accessLower accessUpper small credit debit
  exact ⟨advance, by have nextCovered := advance.covered; omega⟩

end InitECandidate.Solver.GasBudget.ForwardCredit

#print axioms InitECandidate.Solver.GasBudget.ForwardCredit.memory_advance
