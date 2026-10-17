import InitECandidate.Solver.WitnessRadix.BackingLayout

namespace InitECandidate.Solver.WitnessRadix.BackingLayout

def ReadOffset (layout : Layout) : Pool → Nat → Prop
  | .header, offset => offset = 32 ∨ offset = 40
  | .keys, offset => ∃ index < layout.count, ∃ limb < 4, offset = 32 * index + 8 * limb
  | .vals, offset => ∃ index < layout.count, offset = 8 * index
  | .records, offset => ∃ index < layout.count, ∃ field < 2, offset = 16 * index + 8 * field
  | .primary, _ | .backup, _ => False

def WriteOffset (layout : Layout) : Pool → Nat → Prop
  | .header, offset => offset = 24
  | .keys, offset => ∃ node < layout.count, ∃ field < 3, offset = 32 * layout.count + 24 * node + 8 * field
  | .vals, offset => ∃ depth < layout.count, offset = 8 * layout.count + 8 * depth
  | .primary, offset | .backup, offset => ∃ index < layout.capacity, offset = 8 * index
  | .records, _ => False

theorem read_offset_bound (layout : Layout) (valid : Valid layout) (pool : Pool) (offset : Nat)
    (read : ReadOffset layout pool offset) : offset < size layout pool := by
  have room := valid.room
  cases pool with
  | header => rcases read with rfl | rfl <;> simp only [size] <;> decide
  | keys => rcases read with ⟨index, bound, limb, limbBound, rfl⟩; change _ < 32 * layout.capacity; omega
  | vals => rcases read with ⟨index, bound, rfl⟩; change _ < 8 * layout.capacity; omega
  | records => rcases read with ⟨index, bound, field, fieldBound, rfl⟩; change _ < 16 * layout.count; omega
  | primary | backup => exact False.elim read

theorem write_offset_bound (layout : Layout) (valid : Valid layout) (pool : Pool) (offset : Nat)
    (write : WriteOffset layout pool offset) : offset < size layout pool := by
  have room := valid.room
  cases pool with
  | header =>
      rcases write with rfl
      change 24 < 72
      decide
  | keys => rcases write with ⟨node, bound, field, fieldBound, rfl⟩; change _ < 32 * layout.capacity; omega
  | vals => rcases write with ⟨depth, bound, rfl⟩; change _ < 8 * layout.capacity; omega
  | primary | backup => rcases write with ⟨index, bound, rfl⟩ <;> change _ < 8 * layout.capacity <;> omega
  | records => exact False.elim write

theorem read_write_offset_ne (layout : Layout) (pool : Pool) (left right : Nat)
    (read : ReadOffset layout pool left) (write : WriteOffset layout pool right) : left ≠ right := by
  cases pool with
  | header => rcases read with rfl | rfl <;> rcases write with rfl <;> decide
  | keys =>
      rcases read with ⟨index, bound, limb, limbBound, rfl⟩
      rcases write with ⟨node, nodeBound, field, fieldBound, rfl⟩
      omega
  | vals =>
      rcases read with ⟨index, bound, rfl⟩
      rcases write with ⟨depth, depthBound, rfl⟩
      omega
  | primary | backup => exact False.elim read
  | records => exact False.elim write

theorem read_write_separate (layout : Layout) (valid : Valid layout) (leftPool rightPool : Pool) (left right : Nat)
    (read : ReadOffset layout leftPool left) (write : WriteOffset layout rightPool right) :
    cell layout leftPool left ≠ cell layout rightPool right := by
  by_cases same : leftPool = rightPool
  · subst rightPool
    exact cell_injective layout valid leftPool left right (read_offset_bound layout valid _ _ read)
      (write_offset_bound layout valid _ _ write) (read_write_offset_ne layout _ _ _ read write)
  · exact valid.separate leftPool rightPool same left (read_offset_bound layout valid _ _ read)
      right (write_offset_bound layout valid _ _ write)

theorem leaf_reads_classified (layout : Layout) (query : BitVec 64) (read : leafReads layout query) :
    ∃ pool offset, ReadOffset layout pool offset ∧ query = cell layout pool offset := by
  rcases read with headerKeys | headerVals | values | records | keys
  · exact ⟨.header, 32, Or.inl rfl, headerKeys⟩
  · exact ⟨.header, 40, Or.inr rfl, headerVals⟩
  · obtain ⟨index, bound, word⟩ := values
    exact ⟨.vals, _, ⟨index, bound, rfl⟩, word⟩
  · obtain ⟨index, bound, field, fieldBound, word⟩ := records
    exact ⟨.records, _, ⟨index, bound, field, fieldBound, rfl⟩, word⟩
  · obtain ⟨index, bound, limb, limbBound, word⟩ := keys
    exact ⟨.keys, _, ⟨index, bound, limb, limbBound, rfl⟩, word⟩

/-- Every radix-construction write zone is disjoint from every immutable
leaf read, derived uniformly from allocation extents and prefix/suffix bounds. -/
theorem leaf_write_separate (layout : Layout) (valid : Valid layout) (query : BitVec 64)
    (read : leafReads layout query) (pool : Pool) (offset : Nat) (write : WriteOffset layout pool offset) :
    query ≠ cell layout pool offset := by
  obtain ⟨readPool, readOffset, classified, rfl⟩ := leaf_reads_classified layout query read
  exact read_write_separate layout valid readPool pool readOffset offset classified write

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.read_write_separate
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_write_separate
