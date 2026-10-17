import InitECandidate.Solver.WitnessRadix.LayoutLeafMemory
import InitECandidate.Solver.WitnessRadix.LayoutLocationStep

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

def completedLeaf (context : SplitContext) (sliceFor : BitVec 64 → Graph.Slice) (ordinal : Nat) : OpenGraph.Tree :=
  .complete context.dest (WordBits.leafTag ordinal)
    (.leaf (context.keyFor (BitVec.ofNat 64 ordinal)) (sliceFor (BitVec.ofNat 64 ordinal)))

/-- A valid terminal ordinal fills the active graph hole with its exact
original key/slice, from the common layout and immutable-record invariant. -/
theorem fill_leaf_graph {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (mapped : Mapped source layout) (branchRoom : allocated < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor)
    (ordinal : Nat) (inside : ordinal < layout.count) (before after : OpenGraph.Tree)
    (step : OpenGraph.FillFirst context.dest
      (.leaf (context.keyFor (BitVec.ofNat 64 ordinal)) (sliceFor (BitVec.ofNat 64 ordinal)))
      (completedLeaf context sliceFor ordinal) before after)
    (rep : OpenGraph.Represents source layout.table layout.keys layout.vals before)
    (safe : OpenGraph.SafeFrontier source layout.table layout.keys layout.vals before) :
    OpenGraph.Represents (OpenGraph.leafPost source context.dest ordinal) layout.table layout.keys layout.vals after ∧
      OpenGraph.expected after = OpenGraph.expected before := by
  obtain ⟨pool, offset, write, destEq⟩ := destination_writable layout context allocated depth destination atLayout branchRoom
  have destinationMapped : source.memaddrs context.dest := by
    rw [destEq]
    have bound := write_word_bound layout valid pool offset write
    exact mapped pool offset bound.2 bound.1
  have active : ∃ expected, (context.dest, expected) ∈ OpenGraph.frontier before := by
    obtain ⟨pending, oldFrontier, nextFrontier⟩ := OpenGraph.fill_frontier step
    exact ⟨.leaf (context.keyFor (BitVec.ofNat 64 ordinal)) (sliceFor (BitVec.ofNat 64 ordinal)),
      by rw [oldFrontier]; exact List.mem_cons_self⟩
  have small : ordinal < 2 ^ 63 := Nat.lt_trans inside (count_small layout valid)
  refine ⟨OpenGraph.replacement_represents source (OpenGraph.leafPost source context.dest ordinal) rfl rfl
    layout.table layout.keys layout.vals (OpenGraph.fill_replaces step) rfl ?_
    (leaf_graph_agreement source layout context before ordinal safe active) rep,
    OpenGraph.replacement_expected (OpenGraph.fill_replaces step) rfl⟩
  exact OpenGraph.new_leaf source layout.table layout.keys layout.vals context.dest (record layout ordinal)
    (sliceFor (BitVec.ofNat 64 ordinal)).1 (sliceFor (BitVec.ofNat 64 ordinal)).2 ordinal
    (context.keyFor (BitVec.ofNat 64 ordinal)) small destinationMapped
    (immutable_leaf_cells source layout context.keyFor sliceFor immutable ordinal inside)
    (immutable.views ordinal inside) (hash_fits layout valid ordinal inside)
    (leaf_key_away source layout context allocated depth destination atLayout valid branchRoom sliceFor immutable ordinal inside)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.fill_leaf_graph
