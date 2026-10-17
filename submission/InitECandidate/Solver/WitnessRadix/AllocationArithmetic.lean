import InitECandidate.Solver.WitnessRadix.PersistentAlloc

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc

theorem rounded_shift (pointer amount : BitVec 64) :
    rounded pointer amount = ((pointer + amount + 7#64) >>> (3 : Nat)) <<< (3 : Nat) := by
  rw [BitVec.shiftLeft_ushiftRight]
  rfl

theorem rounded_nat (pointer amount : BitVec 64)
    (fits : pointer.toNat + amount.toNat + 7 < 2 ^ 64) :
    (rounded pointer amount).toNat = (pointer.toNat + amount.toNat + 7) / 8 * 8 := by
  have sum : (pointer + amount + 7#64).toNat = pointer.toNat + amount.toNat + 7 := by
    rw [BitVec.toNat_add_of_lt (by
      have first : (pointer + amount).toNat = pointer.toNat + amount.toNat :=
        BitVec.toNat_add_of_lt (by omega)
      rw [first]; exact fits), BitVec.toNat_add_of_lt (by omega)]
    rfl
  rw [rounded_shift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, sum,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change ((_ / 8) * 8) % 2 ^ 64 = _
  rw [Nat.mod_eq_of_lt (by omega)]

theorem rounded_aligned (pointer amount : BitVec 64)
    (fits : pointer.toNat + amount.toNat + 7 < 2 ^ 64) :
    (rounded pointer amount).toNat % 8 = 0 := by
  rw [rounded_nat pointer amount fits]
  omega

/-- Natural heap-room facts imply both actual guards, no overflow, monotone
allocation and the exact aligned next pointer. -/
theorem guards (pointer amount : BitVec 64)
    (fits : pointer.toNat + amount.toNat ≤ 33806089496) :
    (¬ heapEnd - pointer < amount) ∧ (¬ heapEnd < rounded pointer amount) ∧
      pointer.toNat + amount.toNat ≤ (rounded pointer amount).toNat ∧
      (rounded pointer amount).toNat ≤ 33806089496 ∧ (rounded pointer amount).toNat % 8 = 0 := by
  have noWrap : pointer.toNat + amount.toNat + 7 < 2 ^ 64 := by omega
  have number := rounded_nat pointer amount noWrap
  have aligned := rounded_aligned pointer amount noWrap
  have pointerLe : pointer ≤ heapEnd := by change pointer.toNat ≤ 33806089496; omega
  have difference := BitVec.toNat_sub_of_le pointerLe
  change (heapEnd - pointer).toNat = 33806089496 - pointer.toNat at difference
  refine ⟨?_, ?_, ?_, ?_, aligned⟩
  · change ¬ (heapEnd - pointer).toNat < amount.toNat
    rw [difference]
    omega
  · change ¬ 33806089496 < (rounded pointer amount).toNat
    omega
  · omega
  · omega

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.rounded_nat
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.guards
