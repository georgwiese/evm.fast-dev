import InitECandidate.Solver.GasBudget.ForwardCredit

namespace InitECandidate.Solver.GasBudget.ForwardCredit
open Flapjack

/-- Affordability excludes the saturation sentinel, so the real up-front
CALL fee covers memory expansion plus the stipend and at least100 more gas. -/
theorem memory_surplus (words : U256Zero.Quad) (access memoryCost : BitVec 64)
    (accessLower : 100 ≤ access.toNat) (accessUpper : access.toNat ≤ 3000)
    (affordable : (SaturatingAdd.resultWord (access + valueFee words) memoryCost).toNat ≤ 16777216) :
    memoryCost.toNat + (CallGas.stipend words).toNat + 100 ≤
      (SaturatingAdd.resultWord (access + valueFee words) memoryCost).toNat := by
  have number := SaturatingAdd.result_nat (access + valueFee words) memoryCost
  have stipend := surplus words access 0#64 accessLower accessUpper
  have zero := SaturatingAdd.result_nat (access + valueFee words) 0#64
  have feeSmall : (valueFee words).toNat ≤ 11300 := by
    unfold valueFee
    split <;> decide
  have sum : (access + valueFee words).toNat = access.toNat + (valueFee words).toNat :=
    BitVec.toNat_add_of_lt (by change access.toNat + (valueFee words).toNat < 2^64; omega)
  change (CallGas.stipend words).toNat + 100 ≤ _ at stipend
  change (SaturatingAdd.resultWord (access + valueFee words) 0#64).toNat = min (2^64 - 1) ((access + valueFee words).toNat + 0) at zero
  rw [sum] at number zero
  omega

/-- A real first-charge credit followed by the actual forward debit retains
the whole old-used-plus-expansion coverage and100 strict progress. -/
theorem after_forward (oldUsed chargedUsed forwardedUsed : Nat) (words : U256Zero.Quad) (access memoryCost : BitVec 64)
    (accessLower : 100 ≤ access.toNat) (accessUpper : access.toNat ≤ 3000)
    (affordable : (SaturatingAdd.resultWord (access + valueFee words) memoryCost).toNat ≤ 16777216)
    (credit : oldUsed + (SaturatingAdd.resultWord (access + valueFee words) memoryCost).toNat ≤ chargedUsed)
    (debit : forwardedUsed + (CallGas.stipend words).toNat = chargedUsed) :
    oldUsed + memoryCost.toNat + 100 ≤ forwardedUsed := by
  have paid := memory_surplus words access memoryCost accessLower accessUpper affordable
  omega

end InitECandidate.Solver.GasBudget.ForwardCredit

#print axioms InitECandidate.Solver.GasBudget.ForwardCredit.memory_surplus
#print axioms InitECandidate.Solver.GasBudget.ForwardCredit.after_forward
