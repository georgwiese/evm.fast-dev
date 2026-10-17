import InitECandidate.Solver.WitnessRadix.Space

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

/-- Pending-task arrays occupy the unused tails of the baseline arrays.
The prefix holds N data elements and the suffix holds at most N task elements. -/
theorem pending_cell_fits (records capacity depth : Nat)
    (room : 2 * records + 2 ≤ capacity) (active : depth < records) :
    8 * records + 8 * depth + 8 ≤ 8 * capacity := by omega

theorem prefix_pending_separate (base : BitVec 64) (records capacity index depth : Nat)
    (room : 2 * records + 2 ≤ capacity)
    (dataIndex : index < records) (taskIndex : depth < records)
    (allocation : base.toNat + 8 * capacity < 2 ^ 64) :
    byteAddress base (8 * index) ≠ byteAddress base (8 * records + 8 * depth) := by
  apply byteAddress_ne
  · omega
  · omega
  · omega

/-- Hash words and branch words share the original key allocation without
overlap. A branch has three aligned words and is placed after all N hashes. -/
theorem hash_branch_separate (base : BitVec 64) (records capacity hashRow limb node field : Nat)
    (room : 2 * records + 2 ≤ capacity)
    (hashIndex : hashRow < records) (limbIndex : limb < 4)
    (nodeIndex : node < records) (fieldIndex : field < 3)
    (allocation : base.toNat + 32 * capacity < 2 ^ 64) :
    byteAddress base (32 * hashRow + 8 * limb) ≠
      byteAddress base (32 * records + 24 * node + 8 * field) := by
  apply byteAddress_ne
  · omega
  · omega
  · omega

/-- Two distinct words of the branch arena cannot alias. -/
theorem branch_cells_injective (base : BitVec 64) (records capacity nodeA nodeB fieldA fieldB : Nat)
    (room : 2 * records + 2 ≤ capacity)
    (a : nodeA < records) (b : nodeB < records)
    (fa : fieldA < 3) (fb : fieldB < 3)
    (different : nodeA ≠ nodeB ∨ fieldA ≠ fieldB)
    (allocation : base.toNat + 32 * capacity < 2 ^ 64) :
    byteAddress base (32 * records + 24 * nodeA + 8 * fieldA) ≠
      byteAddress base (32 * records + 24 * nodeB + 8 * fieldB) := by
  apply byteAddress_ne
  · omega
  · omega
  · omega

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.byteAddress_toNat
#print axioms InitECandidate.Solver.WitnessRadix.prefix_pending_separate
#print axioms InitECandidate.Solver.WitnessRadix.hash_branch_separate
#print axioms InitECandidate.Solver.WitnessRadix.branch_cells_injective
