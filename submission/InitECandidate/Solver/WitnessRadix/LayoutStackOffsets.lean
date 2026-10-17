import InitECandidate.Solver.WitnessRadix.LayoutPendingReads

namespace InitECandidate.Solver.WitnessRadix.BackingLayout

def StackOffset (layout : Layout) (allocated depth : Nat) : Pool → Nat → Prop
  | .primary, offset | .backup, offset | .vals, offset => ∃ index < depth, offset = 8 * layout.count + 8 * index
  | .keys, offset => ∃ node < allocated, offset = 32 * layout.count + 24 * node
  | .header, _ | .records, _ => False

theorem stack_zone_classified (layout : Layout) (allocated depth : Nat) (query : BitVec 64)
    (zone : StackReadZone layout allocated depth query) :
    ∃ pool offset, StackOffset layout allocated depth pool offset ∧ query = cell layout pool offset := by
  rcases zone with suffix | parent
  · obtain ⟨pool, selected, index, bound, word⟩ := suffix
    refine ⟨pool, _, ?_, word⟩
    rcases selected with rfl | rfl | rfl <;> exact ⟨index, bound, rfl⟩
  · obtain ⟨index, bound, word⟩ := parent
    exact ⟨.keys, _, ⟨index, bound, rfl⟩, word⟩

theorem stack_offset_bound (layout : Layout) (valid : Valid layout) (allocated depth : Nat)
    (branches : allocated ≤ layout.count) (stack : depth ≤ layout.count) (pool : Pool) (offset : Nat)
    (read : StackOffset layout allocated depth pool offset) : offset < size layout pool := by
  have room := valid.room
  cases pool with
  | primary | backup | vals =>
      obtain ⟨index, bound, rfl⟩ := read
      change _ < 8 * layout.capacity
      omega
  | keys =>
      obtain ⟨node, bound, rfl⟩ := read
      change _ < 32 * layout.capacity
      omega
  | header | records => exact False.elim read

theorem stack_prefix_offset_ne (layout : Layout) (allocated depth : Nat) (pool : Pool) (offset index : Nat)
    (buffer : pool = .primary ∨ pool = .backup) (read : StackOffset layout allocated depth pool offset)
    (indexBound : index < layout.count) : offset ≠ 8 * index := by
  rcases buffer with rfl | rfl <;> obtain ⟨slot, bound, rfl⟩ := read <;> omega

theorem stack_prefix_separate (layout : Layout) (valid : Valid layout) (allocated depth : Nat)
    (branches : allocated ≤ layout.count) (stack : depth ≤ layout.count) (query : BitVec 64)
    (zone : StackReadZone layout allocated depth query) (pool : Pool) (buffer : pool = .primary ∨ pool = .backup)
    (index : Nat) (indexBound : index < layout.count) : query ≠ cell layout pool (8 * index) := by
  obtain ⟨readPool, readOffset, read, rfl⟩ := stack_zone_classified layout allocated depth query zone
  have readBound := stack_offset_bound layout valid allocated depth branches stack readPool readOffset read
  have writeBound : 8 * index < size layout pool := by
    have room := valid.room
    rcases buffer with rfl | rfl <;> change _ < 8 * layout.capacity <;> omega
  by_cases same : readPool = pool
  · subst readPool
    exact cell_injective layout valid pool readOffset (8 * index) readBound writeBound
      (stack_prefix_offset_ne layout allocated depth pool readOffset index buffer read indexBound)
  · exact valid.separate readPool pool same readOffset readBound _ writeBound

/-- A lower pending-stack cell or old parent-bit word cannot be any of the
new branch, active child-slot or current stack-push destinations. -/
theorem stack_not_allocation (layout : Layout) (allocated depth : Nat) (pool : Pool) (offset : Nat)
    (read : StackOffset layout allocated depth pool offset) (destination : Address)
    (incoming : IncomingOffset layout allocated destination.1 destination.2) :
    (pool, offset) ∉ allocationAddresses layout allocated depth destination := by
  obtain ⟨destPool, destOffset⟩ := destination
  cases destPool with
  | header =>
      rcases incoming with rfl
      cases pool with
      | primary | backup | vals =>
          obtain ⟨index, bound, rfl⟩ := read
          simp [allocationAddresses] <;> omega
      | keys =>
          obtain ⟨node, bound, rfl⟩ := read
          simp [allocationAddresses] <;> omega
      | header | records => exact False.elim read
  | keys =>
      obtain ⟨old, oldBound, field, fields, rfl⟩ := incoming
      rcases fields with rfl | rfl
      all_goals cases pool with
      | primary | backup | vals =>
          obtain ⟨index, bound, rfl⟩ := read
          simp [allocationAddresses] <;> omega
      | keys =>
          obtain ⟨node, bound, rfl⟩ := read
          simp [allocationAddresses] <;> omega
      | header | records => exact False.elim read
  | primary | backup | vals | records => exact False.elim incoming

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.stack_prefix_separate
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.stack_not_allocation
