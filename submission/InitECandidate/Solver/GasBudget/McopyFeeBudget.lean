import InitECandidate.Solver.GasBudget.McopyCopyGuard

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Input.RlpWrite

theorem fee_number (len : U256Value.Words) :
    (wordFee len).toNat = 3 + 3 * (WordsOf.resultWord (SatWord.resultWord len)).toNat :=
  (WordsOf.fee_numbers _ (WordsOf.upper _) 3 3 (by decide) (by decide)).1

theorem charge_covers_fee (src dst len : U256Value.Words) (current : BitVec 64) :
    3 + 3 * (WordsOf.resultWord (SatWord.resultWord len)).toNat ≤ (chargeWord src dst len current).toNat := by
  rw [← fee_number]
  exact BitVec.le_def.mp (SaturatingAdd.ge_left _ _)

theorem guard_credit (base mark current : BitVec 64) (src dst len : U256Value.Words) :
    3 * guardPrice base mark src dst len ≤ 8 * (chargeWord src dst len current).toNat + 57 := by
  have fee := charge_covers_fee src dst len current
  have words := WordsOf.lower (SatWord.resultWord len)
  have blocks := guard_blocks base mark src dst len
  have division32 := Nat.mod_add_div (SatWord.resultWord len).toNat 32
  have division8 := Nat.mod_add_div (SatWord.resultWord len).toNat 8
  omega

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.fee_number
#print axioms InitECandidate.Solver.GasBudget.Mcopy.charge_covers_fee
#print axioms InitECandidate.Solver.GasBudget.Mcopy.guard_credit
