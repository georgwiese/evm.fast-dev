import InitECandidate.Solver.WitnessRadix.LayoutContext

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem context_allocation_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (mapped : Mapped source layout) (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count) :
    SplitProgram.Mapped source context.node context.depth context.dest context.pendingStart context.pendingCount context.pendingNode := by
  have allMapped (word : BitVec 64) (member : word ∈ (SplitCount.writes context).map Prod.fst) : source.memaddrs word := by
    obtain ⟨pool, offset, write, rfl⟩ := allocation_writable layout context allocated depth destination atLayout valid branchRoom stackRoom word member
    have bound := write_word_bound layout valid pool offset write
    exact mapped pool offset bound.2 bound.1
  exact ⟨allMapped _ (by simp [SplitCount.writes, SplitProgram.allocationWrites]),
    allMapped _ (by simp [SplitCount.writes, SplitProgram.allocationWrites]),
    allMapped _ (by simp [SplitCount.writes, SplitProgram.allocationWrites]),
    allMapped _ (by simp [SplitCount.writes, SplitProgram.allocationWrites]),
    allMapped _ (by simp [SplitCount.writes, SplitProgram.allocationWrites]),
    allMapped _ (by simp [SplitCount.writes, SplitProgram.allocationWrites]),
    allMapped _ (by simp [SplitCount.writes, SplitProgram.allocationWrites])⟩

/-- The shared allocation invariant derives preservation of every immutable
record/key cell through the full actual split memory update. -/
theorem split_immutable {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor) :
    Immutable (SplitCount.post source context) layout context.keyFor sliceFor := by
  have room := valid.room
  apply immutable_of_agreement source (SplitCount.post source context) layout valid context.keyFor sliceFor rfl rfl _ immutable
  intro query read
  apply Eq.symm
  apply SplitCount.post_away source context query
  · intro offset bound
    have rowEq : BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) =
        cell layout .primary (8 * (context.start + offset)) := by
      rw [atLayout.srcEq]
      exact row_cell layout .primary context.start offset
    rw [rowEq]
    exact leaf_write_separate layout valid query read .primary _
      ⟨context.start + offset, by have := atLayout.interval; omega, rfl⟩
  · intro offset bound
    have rowEq : BuildCopy.row context.dst (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) =
        cell layout .backup (8 * (context.start + offset)) := by
      rw [atLayout.dstEq]
      exact row_cell layout .backup context.start offset
    rw [rowEq]
    exact leaf_write_separate layout valid query read .backup _
      ⟨context.start + offset, by have := atLayout.interval; omega, rfl⟩
  · intro member
    obtain ⟨pool, offset, write, equal⟩ := allocation_writable layout context allocated depth destination atLayout valid branchRoom stackRoom query member
    exact leaf_write_separate layout valid query read pool offset write equal

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.context_allocation_mapped
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_immutable
