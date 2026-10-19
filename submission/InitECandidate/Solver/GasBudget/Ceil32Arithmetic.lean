import InitECandidate.Solver.GasBudget.Ceil32Value

namespace InitECandidate.Solver.GasBudget.Ceil32
open Flapjack

theorem remainder_nat (v : BitVec 64) : (remainder v).toNat = v.toNat % 32 := by
  rw [remainder, BitVec.toNat_and]
  change v.toNat &&& (2 ^ 5 - 1) = v.toNat % 32
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- Exact natural saturation/rounding formula for the original ceil32. -/
theorem result_nat (v : BitVec 64) : (resultWord v).toNat = min (2 ^ 64 - 1) (32 * ((v.toNat + 31) / 32)) := by
  have remainderBound := Nat.mod_lt v.toNat (by decide : 0 < 32)
  have division := Nat.mod_add_div v.toNat 32
  have nextDivision := Nat.mod_add_div (v.toNat + 31) 32
  have nextRemainder := Nat.mod_lt (v.toNat + 31) (by decide : 0 < 32)
  have number := remainder_nat v
  have bound := v.isLt
  by_cases zero : remainder v = 0#64
  · have remZero := congrArg BitVec.toNat zero
    change (remainder v).toNat = 0 at remZero
    rw [number] at remZero
    rw [resultWord, if_pos zero]
    omega
  · have remPositive : 0 < (remainder v).toNat := by
      by_contra notPositive
      apply zero
      apply BitVec.eq_of_toNat_eq
      change (remainder v).toNat = 0
      omega
    have order : remainder v ≤ 32#64 := by change (remainder v).toNat ≤ 32; omega
    rw [resultWord, if_neg zero, SaturatingAdd.result_nat, BitVec.toNat_sub_of_le order]
    change min (2 ^ 64 - 1) (v.toNat + (32 - (remainder v).toNat)) = _
    rw [number]
    congr 1
    omega

theorem fixed_of_aligned (v : BitVec 64) (aligned : v.toNat % 32 = 0) : resultWord v = v := by
  have zero : remainder v = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    change (remainder v).toNat = 0
    rw [remainder_nat, aligned]
  rw [resultWord, if_pos zero]

theorem aligned_or_max (v : BitVec 64) : (resultWord v).toNat % 32 = 0 ∨ resultWord v = 18446744073709551615#64 := by
  have number := result_nat v
  by_cases fits : 32 * ((v.toNat + 31) / 32) ≤ 2 ^ 64 - 1
  · apply Or.inl
    rw [number, Nat.min_eq_right fits]
    simp
  · apply Or.inr
    apply BitVec.eq_of_toNat_eq
    change (resultWord v).toNat = 2 ^ 64 - 1
    rw [number]
    omega

theorem aligned_of_not_max (v : BitVec 64) (notMax : resultWord v ≠ 18446744073709551615#64) :
    (resultWord v).toNat % 32 = 0 := (aligned_or_max v).resolve_right notMax

theorem idempotent_of_not_max (v : BitVec 64) (notMax : resultWord v ≠ 18446744073709551615#64) :
    resultWord (resultWord v) = resultWord v := fixed_of_aligned _ (aligned_of_not_max v notMax)

end InitECandidate.Solver.GasBudget.Ceil32

#print axioms InitECandidate.Solver.GasBudget.Ceil32.result_nat
#print axioms InitECandidate.Solver.GasBudget.Ceil32.fixed_of_aligned
#print axioms InitECandidate.Solver.GasBudget.Ceil32.aligned_of_not_max
#print axioms InitECandidate.Solver.GasBudget.Ceil32.idempotent_of_not_max
