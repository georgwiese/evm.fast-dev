import InitECandidate.Solver.WitnessRadix.ByteKeys

namespace InitECandidate.Solver.WitnessRadix.WordBits

theorem mask7 (word : BitVec 64) : (word &&& 7#64).toNat = word.toNat % 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat 3

theorem shift3 (word : BitVec 64) : (word >>> 3).toNat = word.toNat / 8 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The exact 64-bit branch expression applied to a zero-extended byte. -/
def digit (byte : BitVec 8) (position : BitVec 64) : BitVec 64 :=
  ((byte.setWidth 64) >>> (position &&& 7#64).toNat) &&& 1#64

theorem digit_eq (byte : BitVec 8) (position : BitVec 64) :
    digit byte position = BitVec.ofNat 64 (byte.getLsbD (position.toNat % 8)).toNat := by
  unfold digit
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD, mask7]
  simp only [BitVec.getLsbD_ushiftRight, Nat.add_zero, BitVec.getLsbD_setWidth]
  have small : position.toNat % 8 < 64 := by omega
  simp only [small, decide_true, Bool.true_and]
  cases byte.getLsbD (position.toNat % 8) <;> rfl

theorem digit_zero (byte : BitVec 8) (position : BitVec 64) :
    digit byte position = 0#64 ↔ byte.getLsbD (position.toNat % 8) = false := by
  rw [digit_eq]
  cases byte.getLsbD (position.toNat % 8) <;> decide

theorem implementation_bit (readByte : BitVec 64 → BitVec 8) (pointer : BitVec 64)
    (position : BitVec 64) (inside : position.toNat < 256) :
    digit (readByte (pointer + (position >>> 3))) position =
      BitVec.ofNat 64 (ByteKeys.bit (ByteKeys.keyAt readByte pointer) position.toNat).toNat := by
  rw [ByteKeys.bit_at readByte pointer position.toNat inside, digit_eq]
  have index : position >>> 3 = BitVec.ofNat 64 (position.toNat / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [shift3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := position.isLt
    omega
  rw [index]

def leafTag (ordinal : Nat) : BitVec 64 := BitVec.ofNat 64 (2 * ordinal + 1)

theorem leafTag_toNat (ordinal : Nat) (small : ordinal < 2 ^ 63) :
    (leafTag ordinal).toNat = 2 * ordinal + 1 := by
  unfold leafTag
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  omega

theorem leafTag_nonzero (ordinal : Nat) (small : ordinal < 2 ^ 63) :
    leafTag ordinal ≠ 0#64 := by
  intro equal
  have natEq := congrArg BitVec.toNat equal
  rw [leafTag_toNat ordinal small] at natEq
  change 2 * ordinal + 1 = 0 at natEq
  omega

theorem leafTag_odd (ordinal : Nat) (small : ordinal < 2 ^ 63) :
    leafTag ordinal &&& 1#64 = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, leafTag_toNat ordinal small]
  change (2 * ordinal + 1) &&& (2 ^ 1 - 1) = 1
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem leafTag_decode (ordinal : Nat) (small : ordinal < 2 ^ 63) :
    leafTag ordinal >>> 1 = BitVec.ofNat 64 ordinal := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, leafTag_toNat ordinal small,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

end InitECandidate.Solver.WitnessRadix.WordBits

#print axioms InitECandidate.Solver.WitnessRadix.WordBits.implementation_bit
#print axioms InitECandidate.Solver.WitnessRadix.WordBits.leafTag_nonzero
#print axioms InitECandidate.Solver.WitnessRadix.WordBits.leafTag_odd
#print axioms InitECandidate.Solver.WitnessRadix.WordBits.leafTag_decode
