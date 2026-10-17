import InitECandidate.Solver.WitnessRadix.BackingLayout
import InitECandidate.Solver.WitnessRadix.QueryFootprint

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact

def record (layout : Layout) (index : Nat) : BitVec 64 := cell layout .records (16 * index)

structure Immutable {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice) : Prop where
  keysMapped : source.memaddrs (cell layout .header 32)
  keysWord : source.memory (cell layout .header 32) = .word layout.keys
  valsMapped : source.memaddrs (cell layout .header 40)
  valsWord : source.memory (cell layout .header 40) = .word layout.vals
  recordMapped : ∀ index < layout.count, source.memaddrs (cell layout .vals (8 * index))
  recordWord : ∀ index < layout.count, source.memory (cell layout .vals (8 * index)) = .word (record layout index)
  pointerMapped : ∀ index < layout.count, source.memaddrs (cell layout .records (16 * index))
  lengthMapped : ∀ index < layout.count, source.memaddrs (cell layout .records (16 * index + 8))
  pointerWord : ∀ index < layout.count,
    source.memory (cell layout .records (16 * index)) = .word (sliceFor (BitVec.ofNat 64 index)).1
  lengthWord : ∀ index < layout.count,
    source.memory (cell layout .records (16 * index + 8)) = .word (sliceFor (BitVec.ofNat 64 index)).2
  views : ∀ index < layout.count,
    MemoryBytes.ByteView source (layout.keys + BitVec.ofNat 64 index * 32#64) (keyFor (BitVec.ofNat 64 index))

theorem record_next (layout : Layout) (index : Nat) :
    record layout index + 8#64 = cell layout .records (16 * index + 8) := by
  simp only [record, cell, base, byteAddress, BitVec.ofNat_add, BitVec.add_assoc]

theorem vals_cell (layout : Layout) (index : Nat) :
    layout.vals + BitVec.ofNat 64 index * 8#64 = cell layout .vals (8 * index) := by
  change layout.vals + BitVec.ofNat 64 index * BitVec.ofNat 64 8 = layout.vals + BitVec.ofNat 64 (8 * index)
  rw [Nat.mul_comm 8 index, BitVec.ofNat_mul]

/-- Every valid ordinal supplies the exact concrete leaf-cell premises of
lookup, including the original record pointer and original slice words. -/
theorem immutable_leaf_cells {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (immutable : Immutable source layout keyFor sliceFor) (index : Nat) (inside : index < layout.count) :
    QueryLeaf.LeafCells source layout.table layout.keys layout.vals (BitVec.ofNat 64 index) (record layout index)
      (sliceFor (BitVec.ofNat 64 index)).1 (sliceFor (BitVec.ofNat 64 index)).2 := by
  refine ⟨immutable.keysMapped, immutable.keysWord, immutable.valsMapped, immutable.valsWord,
    ?_, ?_, immutable.pointerMapped index inside, ?_, immutable.pointerWord index inside, ?_⟩
  · rw [vals_cell]; exact immutable.recordMapped index inside
  · rw [vals_cell]; exact immutable.recordWord index inside
  · rw [record_next]; exact immutable.lengthMapped index inside
  · rw [record_next]; exact immutable.lengthWord index inside

/-- The full immutable witness data survives writes outside the fixed header,
record/value prefixes and aligned hash words. -/
theorem immutable_of_agreement {F : Type} (source target : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (agree : ∀ query, leafReads layout query → source.memory query = target.memory query)
    (immutable : Immutable source layout keyFor sliceFor) : Immutable target layout keyFor sliceFor := by
  refine ⟨?_, (agree _ (Or.inl rfl)).symm.trans immutable.keysWord,
    ?_, (agree _ (Or.inr (Or.inl rfl))).symm.trans immutable.valsWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← domain]; exact immutable.keysMapped
  · rw [← domain]; exact immutable.valsMapped
  · intro index inside; rw [← domain]; exact immutable.recordMapped index inside
  · intro index inside
    exact (agree _ (Or.inr (Or.inr (Or.inl ⟨index, inside, rfl⟩)))).symm.trans (immutable.recordWord index inside)
  · intro index inside; rw [← domain]; exact immutable.pointerMapped index inside
  · intro index inside; rw [← domain]; exact immutable.lengthMapped index inside
  · intro index inside
    exact (agree _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨index, inside, 0, by decide, by simp⟩))))).symm.trans
      (immutable.pointerWord index inside)
  · intro index inside
    exact (agree _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨index, inside, 1, by decide, by simp⟩))))).symm.trans
      (immutable.lengthWord index inside)
  · intro index inside
    apply MemoryBytes.byteView_of_cells source target domain endian _ _ _ (immutable.views index inside)
    intro byte
    rw [hash_byte_cell layout valid index inside byte]
    exact agree _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨index, inside, byte.val / 8, by have := byte.isLt; omega, rfl⟩))))

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.immutable_leaf_cells
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.immutable_of_agreement
