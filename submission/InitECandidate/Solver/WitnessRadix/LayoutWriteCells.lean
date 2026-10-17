import InitECandidate.Solver.WitnessRadix.LayoutCells

namespace InitECandidate.Solver.WitnessRadix.BackingLayout

theorem write_word_bound (layout : Layout) (valid : Valid layout) (pool : Pool) (offset : Nat)
    (write : WriteOffset layout pool offset) : offset + 8 ≤ size layout pool ∧ offset % 8 = 0 := by
  have room := valid.room
  cases pool with
  | header =>
      rcases write with rfl
      change 24 + 8 ≤ 72 ∧ 24 % 8 = 0
      decide
  | keys =>
      rcases write with ⟨node, bound, field, fieldBound, rfl⟩
      change _ ≤ 32 * layout.capacity ∧ _
      constructor <;> omega
  | vals =>
      rcases write with ⟨depth, bound, rfl⟩
      change _ ≤ 8 * layout.capacity ∧ _
      constructor <;> omega
  | primary | backup =>
      rcases write with ⟨index, bound, rfl⟩
      change _ ≤ 8 * layout.capacity ∧ _
      constructor <;> omega
  | records => exact False.elim write

theorem allocation_address_write (layout : Layout) (valid : Valid layout) (allocated depth : Nat) (destination : Address)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (incoming : IncomingOffset layout allocated destination.1 destination.2) (entry : Address)
    (member : entry ∈ allocationAddresses layout allocated depth destination) :
    WriteOffset layout entry.1 entry.2 := by
  have room := valid.room
  simp only [allocationAddresses, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨allocated, branchRoom, 0, by decide, by simp⟩
  · exact ⟨allocated, branchRoom, 1, by decide, by simp⟩
  · exact ⟨allocated, branchRoom, 2, by decide, by simp⟩
  · exact incoming_write layout allocated branchRoom _ incoming
  · exact ⟨layout.count + depth, by omega, by omega⟩
  · exact ⟨layout.count + depth, by omega, by omega⟩
  · exact ⟨depth, stackRoom, rfl⟩

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.write_word_bound
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.allocation_address_write
