import InitECandidate.Solver.WitnessRadix.ByteKeys

namespace InitECandidate.Solver.WitnessRadix.WordBits

theorem mask7 (word : BitVec 64) : (word &&& 7#64).toNat = word.toNat % 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat 3

theorem shift3 (word : BitVec 64) : (word >>> (3 : Nat)).toNat = word.toNat / 8 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end InitECandidate.Solver.WitnessRadix.WordBits

#print axioms InitECandidate.Solver.WitnessRadix.WordBits.mask7
#print axioms InitECandidate.Solver.WitnessRadix.WordBits.shift3
