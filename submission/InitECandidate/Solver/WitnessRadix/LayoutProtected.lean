import InitECandidate.Solver.WitnessRadix.LayoutLocated

namespace InitECandidate.Solver.WitnessRadix.BackingLayout

theorem protected_fresh (layout : Layout) (valid : Valid layout) (allocated : Nat) (inside : allocated < layout.count)
    (query : BitVec 64) (protectedRead : Protected layout allocated query) (field : Nat) (fieldBound : field < 3) :
    query ≠ cell layout .keys (32 * layout.count + 24 * allocated + 8 * field) := by
  rcases protectedRead with leaf | header | installed
  · exact leaf_write_separate layout valid query leaf .keys _ ⟨allocated, inside, field, fieldBound, rfl⟩
  · rw [header]
    exact valid.separate .header .keys (by decide) 24 (by change 24 < 72; decide) _
      (write_offset_bound layout valid .keys _ ⟨allocated, inside, field, fieldBound, rfl⟩)
  · obtain ⟨node, old, oldField, oldFieldBound, rfl⟩ := installed
    exact branch_cells_injective layout.keys layout.count layout.capacity node allocated oldField field
      valid.room (by omega) inside oldFieldBound fieldBound (Or.inl (by omega)) (valid.noWrap .keys)

theorem protected_buffer_away (layout : Layout) (valid : Valid layout) (allocated : Nat) (branchRoom : allocated < layout.count)
    (query : BitVec 64) (protectedRead : Protected layout allocated query) (pool : Pool)
    (buffer : pool = .primary ∨ pool = .backup) (index : Nat) (indexBound : index < layout.capacity) :
    query ≠ cell layout pool (8 * index) := by
  have write : WriteOffset layout pool (8 * index) := by
    rcases buffer with rfl | rfl <;> exact ⟨index, indexBound, rfl⟩
  have differentHeader : Pool.header ≠ pool := by rcases buffer with rfl | rfl <;> decide
  have differentKeys : Pool.keys ≠ pool := by rcases buffer with rfl | rfl <;> decide
  have bound := write_offset_bound layout valid pool _ write
  rcases protectedRead with leaf | header | installed
  · exact leaf_write_separate layout valid query leaf pool _ write
  · rw [header]
    exact valid.separate .header pool differentHeader 24 (by change 24 < 72; decide) _ bound
  · obtain ⟨node, old, field, fieldBound, rfl⟩ := installed
    exact valid.separate .keys pool differentKeys _
      (write_offset_bound layout valid .keys _ ⟨node, by omega, field, fieldBound, rfl⟩) _ bound

theorem protected_pending_vals (layout : Layout) (valid : Valid layout) (allocated : Nat) (branchRoom : allocated < layout.count)
    (query : BitVec 64) (protectedRead : Protected layout allocated query) (depth : Nat) (stackRoom : depth < layout.count) :
    query ≠ cell layout .vals (8 * layout.count + 8 * depth) := by
  have write : WriteOffset layout .vals (8 * layout.count + 8 * depth) := ⟨depth, stackRoom, rfl⟩
  have bound := write_offset_bound layout valid .vals _ write
  rcases protectedRead with leaf | header | installed
  · exact leaf_write_separate layout valid query leaf .vals _ write
  · rw [header]
    exact valid.separate .header .vals (by decide) 24 (by change 24 < 72; decide) _ bound
  · obtain ⟨node, old, field, fieldBound, rfl⟩ := installed
    exact valid.separate .keys .vals (by decide) _
      (write_offset_bound layout valid .keys _ ⟨node, by omega, field, fieldBound, rfl⟩) _ bound

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.protected_fresh
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.protected_buffer_away
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.protected_pending_vals
