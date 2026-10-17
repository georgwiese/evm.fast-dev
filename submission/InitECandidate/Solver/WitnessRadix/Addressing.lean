import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.WitnessRadix

/-- Byte offset from an actual 64-bit allocation base. -/
def byteAddress (base : BitVec 64) (offset : Nat) : BitVec 64 :=
  base + BitVec.ofNat 64 offset

theorem byteAddress_toNat (base : BitVec 64) (offset : Nat)
    (noWrap : base.toNat + offset < 2 ^ 64) :
    (byteAddress base offset).toNat = base.toNat + offset := by
  have offsetSmall : offset < 2 ^ 64 := by omega
  have encoded : (BitVec.ofNat 64 offset).toNat = offset := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetSmall]
  unfold byteAddress
  rw [BitVec.toNat_add_of_lt (by rw [encoded]; exact noWrap), encoded]

theorem byteAddress_ne (base : BitVec 64) (left right : Nat)
    (leftFits : base.toNat + left < 2 ^ 64)
    (rightFits : base.toNat + right < 2 ^ 64) (different : left ≠ right) :
    byteAddress base left ≠ byteAddress base right := by
  intro equal
  have same := congrArg BitVec.toNat equal
  rw [byteAddress_toNat base left leftFits, byteAddress_toNat base right rightFits] at same
  omega

theorem byteAddress_aligned (base : BitVec 64) (offset : Nat)
    (baseAligned : base.toNat % 8 = 0) (offsetAligned : offset % 8 = 0)
    (noWrap : base.toNat + offset < 2 ^ 64) :
    (byteAddress base offset).toNat % 8 = 0 := by
  rw [byteAddress_toNat base offset noWrap, Nat.add_mod, baseAligned, offsetAligned]

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.byteAddress_toNat
#print axioms InitECandidate.Solver.WitnessRadix.byteAddress_ne
#print axioms InitECandidate.Solver.WitnessRadix.byteAddress_aligned
