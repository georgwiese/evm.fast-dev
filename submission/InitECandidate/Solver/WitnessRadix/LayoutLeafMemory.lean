import InitECandidate.Solver.WitnessRadix.LayoutStackFrame
import InitECandidate.Solver.WitnessRadix.LayoutGraphFrame
import InitECandidate.Solver.WitnessRadix.LeafGraph

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem destination_writable (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (branchRoom : allocated < layout.count) :
    ∃ pool offset, WriteOffset layout pool offset ∧ context.dest = cell layout pool offset :=
  ⟨destination.1, destination.2, incoming_write layout allocated branchRoom destination atLayout.incoming, atLayout.destEq⟩

theorem leaf_immutable {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout) (branchRoom : allocated < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor) (ordinal : Nat) :
    Immutable (OpenGraph.leafPost source context.dest ordinal) layout context.keyFor sliceFor := by
  obtain ⟨pool, offset, write, destEq⟩ := destination_writable layout context allocated depth destination atLayout branchRoom
  apply immutable_of_agreement source (OpenGraph.leafPost source context.dest ordinal) layout valid context.keyFor sliceFor rfl rfl _ immutable
  intro query read
  have away : query ≠ context.dest := by rw [destEq]; exact leaf_write_separate layout valid query read pool offset write
  change source.memory query = StoreWord.put source.memory context.dest (WordBits.leafTag ordinal) query
  simp [StoreWord.put, away]

theorem leaf_graph_agreement {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (tree : OpenGraph.Tree) (ordinal : Nat)
    (safe : OpenGraph.SafeFrontier source layout.table layout.keys layout.vals tree)
    (active : ∃ expected, (context.dest, expected) ∈ OpenGraph.frontier tree) :
    ∀ query, OpenGraph.reads source layout.table layout.keys layout.vals tree query →
      source.memory query = (OpenGraph.leafPost source context.dest ordinal).memory query := by
  intro query read
  have away : query ≠ context.dest := by
    intro same
    subst query
    obtain ⟨expected, member⟩ := active
    exact safe _ member read
  change source.memory query = StoreWord.put source.memory context.dest (WordBits.leafTag ordinal) query
  simp [StoreWord.put, away]

theorem leaf_pending_agreement {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (tasks : List PendingStack.Task) (length : tasks.length = depth) (parents : ParentsWithin layout allocated tasks) (ordinal : Nat) :
    ∀ query, PendingStack.reads context.pendingStart context.pendingCount context.pendingNode tasks query →
      source.memory query = (OpenGraph.leafPost source context.dest ordinal).memory query := by
  intro query read
  rw [atLayout.pendingStartEq, atLayout.pendingCountEq, atLayout.pendingNodeEq] at read
  have zone := pending_read_zone layout allocated tasks parents query read
  rw [length] at zone
  have absent := stack_allocation_separate layout context allocated depth destination atLayout valid branchRoom stackRoom query zone
  have away : query ≠ context.dest := by
    intro same
    subst query
    apply absent
    simp [SplitCount.writes, SplitProgram.allocationWrites]
  change source.memory query = StoreWord.put source.memory context.dest (WordBits.leafTag ordinal) query
  simp [StoreWord.put, away]

theorem leaf_key_away {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout) (branchRoom : allocated < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor)
    (ordinal : Nat) (inside : ordinal < layout.count) :
    ∀ query, QueryMemory.reads source layout.table layout.keys layout.vals (WordBits.leafTag ordinal)
      (.leaf (context.keyFor (BitVec.ofNat 64 ordinal)) (sliceFor (BitVec.ofNat 64 ordinal))) query → query ≠ context.dest := by
  obtain ⟨pool, offset, write, destEq⟩ := destination_writable layout context allocated depth destination atLayout branchRoom
  intro query read
  rw [destEq]
  exact leaf_write_separate layout valid query
    (leaf_read_global source layout valid context.keyFor sliceFor immutable ordinal inside _ _ query read) pool offset write

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_immutable
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_pending_agreement
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_key_away
