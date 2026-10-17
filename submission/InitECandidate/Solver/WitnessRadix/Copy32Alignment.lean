import InitECandidate.Solver.WitnessRadix.Copy32Environment

namespace InitECandidate.Solver.WitnessRadix.Copy32

theorem aligned_mask (pointer : BitVec 64) (aligned : pointer.toNat % 8 = 0) :
    pointer &&& 7#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change pointer.toNat &&& 7 = 0
  rw [show 7 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact aligned

theorem alignment_mask (src dst : BitVec 64)
    (srcAligned : src.toNat % 8 = 0) (dstAligned : dst.toNat % 8 = 0) :
    (dst ||| src) &&& 7#64 = 0#64 := by
  rw [BitVec.and_or_distrib_right, aligned_mask dst dstAligned, aligned_mask src srcAligned]
  rfl

end InitECandidate.Solver.WitnessRadix.Copy32

#print axioms InitECandidate.Solver.WitnessRadix.Copy32.alignment_mask
