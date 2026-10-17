import InitECandidate.Solver.WitnessRadix.LayoutStackOffsets

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem stack_allocation_separate (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count) (query : BitVec 64)
    (zone : StackReadZone layout allocated depth query) : query ∉ (SplitCount.writes context).map Prod.fst := by
  obtain ⟨pool, offset, read, rfl⟩ := stack_zone_classified layout allocated depth query zone
  have readBound := stack_offset_bound layout valid allocated depth (by omega) (by omega) pool offset read
  intro member
  rw [allocation_cells layout context allocated depth destination atLayout] at member
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
  have entryBound := write_offset_bound layout valid _ _
    (allocation_address_write layout valid allocated depth destination branchRoom stackRoom atLayout.incoming entry entryMember)
  have equal := address_injective layout valid entry (pool, offset) entryBound readBound same
  exact stack_not_allocation layout allocated depth pool offset read destination atLayout.incoming (equal ▸ entryMember)

/-- Every old pending suffix/parent read survives a complete actual split;
its frame conditions are consequences of stack depth and layout geometry. -/
theorem split_pending_agreement {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (tasks : List PendingStack.Task) (length : tasks.length = depth) (parents : ParentsWithin layout allocated tasks) :
    ∀ query, PendingStack.reads context.pendingStart context.pendingCount context.pendingNode tasks query →
      source.memory query = (SplitCount.post source context).memory query := by
  intro query read
  rw [atLayout.pendingStartEq, atLayout.pendingCountEq, atLayout.pendingNodeEq] at read
  have zone := pending_read_zone layout allocated tasks parents query read
  rw [length] at zone
  apply Eq.symm
  apply SplitCount.post_away source context query
  · intro offset bound
    have rowEq : BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) =
        cell layout .primary (8 * (context.start + offset)) := by
      rw [atLayout.srcEq]
      exact row_cell layout .primary context.start offset
    rw [rowEq]
    exact stack_prefix_separate layout valid allocated depth (by omega) (by omega) query zone .primary (Or.inl rfl)
      (context.start + offset) (by have := atLayout.interval; omega)
  · intro offset bound
    have rowEq : BuildCopy.row context.dst (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) =
        cell layout .backup (8 * (context.start + offset)) := by
      rw [atLayout.dstEq]
      exact row_cell layout .backup context.start offset
    rw [rowEq]
    exact stack_prefix_separate layout valid allocated depth (by omega) (by omega) query zone .backup (Or.inr rfl)
      (context.start + offset) (by have := atLayout.interval; omega)
  · exact stack_allocation_separate layout context allocated depth destination atLayout valid branchRoom stackRoom query zone

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.stack_allocation_separate
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_pending_agreement
