import InitECandidate.Solver.Arenas.Program
import InitECandidate.Solver.WitnessRadix.AllocationArithmetic

namespace InitECandidate.Solver.Arenas

theorem rounded_down_shift (pointer amount : BitVec 64) :
    rounded .down pointer amount = ((pointer - amount) >>> (3 : Nat)) <<< (3 : Nat) := by
  rw [BitVec.shiftLeft_ushiftRight]
  rfl

theorem rounded_down_nat (pointer amount : BitVec 64) (funded : amount ≤ pointer) :
    (rounded .down pointer amount).toNat = (pointer.toNat - amount.toNat) / 8 * 8 := by
  rw [rounded_down_shift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_sub_of_le funded, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change ((_ / 8) * 8) % 2 ^ 64 = _
  rw [Nat.mod_eq_of_lt (by have bound := pointer.isLt; omega)]

/-- Aligned arena boundaries make the original downward allocator guards
follow from natural room, with less than eight bytes of alignment loss. -/
theorem downward_guards (pointer limit amount : BitVec 64)
    (aligned : limit.toNat % 8 = 0) (room : limit.toNat + amount.toNat ≤ pointer.toNat) :
    (¬ distance .down pointer limit < amount) ∧
      (¬ outside .down (rounded .down pointer amount) limit) ∧
      limit.toNat ≤ (rounded .down pointer amount).toNat ∧
      (rounded .down pointer amount).toNat + amount.toNat ≤ pointer.toNat ∧
      pointer.toNat < (rounded .down pointer amount).toNat + amount.toNat + 8 ∧
      (rounded .down pointer amount).toNat % 8 = 0 := by
  have order : limit ≤ pointer := by change limit.toNat ≤ pointer.toNat; omega
  have funded : amount ≤ pointer := by change amount.toNat ≤ pointer.toNat; omega
  have difference := BitVec.toNat_sub_of_le order
  have number := rounded_down_nat pointer amount funded
  simp only [distance, outside]
  change (¬ (pointer - limit).toNat < amount.toNat) ∧
    (¬ (rounded .down pointer amount).toNat < limit.toNat) ∧ _
  rw [difference, number]
  omega

/-- The actual upward allocator rounds within an aligned live scratch
boundary. Natural room derives both word guards without unsigned wrap. -/
theorem upward_guards (pointer limit amount : BitVec 64)
    (aligned : limit.toNat % 8 = 0) (room : pointer.toNat + amount.toNat ≤ limit.toNat) :
    (¬ distance .up pointer limit < amount) ∧
      (¬ outside .up (rounded .up pointer amount) limit) ∧
      pointer.toNat + amount.toNat ≤ (rounded .up pointer amount).toNat ∧
      (rounded .up pointer amount).toNat ≤ limit.toNat ∧
      (rounded .up pointer amount).toNat < pointer.toNat + amount.toNat + 8 ∧
      (rounded .up pointer amount).toNat % 8 = 0 := by
  have bound := limit.isLt
  have fits : pointer.toNat + amount.toNat + 7 < 2 ^ 64 := by omega
  have order : pointer ≤ limit := by change pointer.toNat ≤ limit.toNat; omega
  have difference := BitVec.toNat_sub_of_le order
  have number : (rounded .up pointer amount).toNat = (pointer.toNat + amount.toNat + 7) / 8 * 8 :=
    WitnessRadix.PersistentAlloc.rounded_nat pointer amount fits
  simp only [distance, outside]
  change (¬ (limit - pointer).toNat < amount.toNat) ∧
    (¬ limit.toNat < (rounded .up pointer amount).toNat) ∧ _
  rw [difference, number]
  omega

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.rounded_down_nat
#print axioms InitECandidate.Solver.Arenas.downward_guards
#print axioms InitECandidate.Solver.Arenas.upward_guards
