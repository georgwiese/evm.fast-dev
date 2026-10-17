import InitECandidate.Solver.WitnessRadix.Addressing

namespace InitECandidate.Solver.WitnessRadix

def branchAddress (keys : BitVec 64) (records allocated : Nat) : BitVec 64 :=
  byteAddress keys (32 * records + 24 * allocated)

theorem branch_address_next (keys : BitVec 64) (records allocated : Nat) :
    branchAddress keys records (allocated + 1) = branchAddress keys records allocated + 24#64 := by
  simp only [branchAddress, byteAddress, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, BitVec.ofNat_add, BitVec.add_assoc]

theorem branch_address_field (keys : BitVec 64) (records allocated field : Nat) :
    branchAddress keys records allocated + BitVec.ofNat 64 (8 * field) =
      byteAddress keys (32 * records + 24 * allocated + 8 * field) := by
  simp only [branchAddress, byteAddress, BitVec.ofNat_add, BitVec.add_assoc]

theorem branch_address_nonzero (keys : BitVec 64) (records capacity allocated : Nat)
    (room : 2 * records + 2 ≤ capacity) (inside : allocated < records)
    (positive : 0 < keys.toNat) (allocation : keys.toNat + 32 * capacity < 2 ^ 64) :
    branchAddress keys records allocated ≠ 0#64 := by
  intro zero
  have number := byteAddress_toNat keys (32 * records + 24 * allocated) (by omega)
  rw [← branchAddress, zero] at number
  change 0 = keys.toNat + (32 * records + 24 * allocated) at number
  omega

theorem branch_address_even (keys : BitVec 64) (records capacity allocated : Nat)
    (room : 2 * records + 2 ≤ capacity) (inside : allocated < records)
    (aligned : keys.toNat % 8 = 0) (allocation : keys.toNat + 32 * capacity < 2 ^ 64) :
    branchAddress keys records allocated &&& 1#64 = 0#64 := by
  have eight : (branchAddress keys records allocated).toNat % 8 = 0 :=
    byteAddress_aligned keys (32 * records + 24 * allocated) aligned (by omega) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (branchAddress keys records allocated).toNat &&& 1 = 0
  rw [show 1 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- A new branch word is distinct from every already installed branch word. -/
theorem branch_address_fresh (keys : BitVec 64) (records capacity allocated old field oldField : Nat)
    (room : 2 * records + 2 ≤ capacity) (inside : allocated < records) (older : old < allocated)
    (fieldBound : field < 3) (oldFieldBound : oldField < 3)
    (allocation : keys.toNat + 32 * capacity < 2 ^ 64) :
    branchAddress keys records allocated + BitVec.ofNat 64 (8 * field) ≠
      branchAddress keys records old + BitVec.ofNat 64 (8 * oldField) := by
  rw [branch_address_field, branch_address_field]
  exact branch_cells_injective keys records capacity allocated old field oldField room inside (by omega)
    fieldBound oldFieldBound (Or.inl (by omega)) allocation

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.branch_address_nonzero
#print axioms InitECandidate.Solver.WitnessRadix.branch_address_even
#print axioms InitECandidate.Solver.WitnessRadix.branch_address_fresh
