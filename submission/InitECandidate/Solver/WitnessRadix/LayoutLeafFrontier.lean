import InitECandidate.Solver.WitnessRadix.LayoutLeafGraph
import InitECandidate.Solver.WitnessRadix.LayoutFrontierSlots

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem leaf_frontier_update {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout) (branchRoom : allocated < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor)
    (ordinal : Nat) (inside : ordinal < layout.count) (before after : OpenGraph.Tree)
    (step : OpenGraph.FillFirst context.dest
      (.leaf (context.keyFor (BitVec.ofNat 64 ordinal)) (sliceFor (BitVec.ofNat 64 ordinal)))
      (completedLeaf context sliceFor ordinal) before after)
    (located : Located layout allocated before)
    (safe : OpenGraph.SafeFrontier source layout.table layout.keys layout.vals before)
    (distinct : ((OpenGraph.frontier before).map Prod.fst).Nodup) :
    OpenGraph.SafeFrontier (OpenGraph.leafPost source context.dest ordinal) layout.table layout.keys layout.vals after ∧
      Located layout allocated after ∧ ((OpenGraph.frontier after).map Prod.fst).Nodup := by
  obtain ⟨pending, oldFrontier, nextFrontier⟩ := OpenGraph.fill_frontier step
  have active : ∃ expected, (context.dest, expected) ∈ OpenGraph.frontier before :=
    ⟨.leaf (context.keyFor (BitVec.ofNat 64 ordinal)) (sliceFor (BitVec.ofNat 64 ordinal)),
      by rw [oldFrontier]; exact List.mem_cons_self⟩
  have agreement := leaf_graph_agreement source layout context before ordinal safe active
  have nextImmutable := leaf_immutable source layout context allocated depth destination atLayout valid branchRoom sliceFor immutable ordinal
  refine ⟨?_, ?_, ?_⟩
  · apply OpenGraph.fill_safe source (OpenGraph.leafPost source context.dest ordinal) layout.table layout.keys layout.vals
      step distinct safe agreement
    · intro entry member
      simp only [completedLeaf, OpenGraph.frontier, List.not_mem_nil] at member
    · intro entry member
      simp only [completedLeaf, OpenGraph.frontier, List.not_mem_nil] at member
    · intro entry member different read
      rcases read with slotRead | leafRead
      · exact different slotRead
      · have globalRead := leaf_read_global (OpenGraph.leafPost source context.dest ordinal) layout valid context.keyFor sliceFor
          nextImmutable ordinal inside _ _ entry.1 leafRead
        obtain ⟨pool, offset, incoming, word⟩ := frontier_incoming layout allocated before located entry member
        exact leaf_write_separate layout valid entry.1 globalRead pool offset
          (incoming_write layout allocated branchRoom (pool, offset) incoming) word
  · have incoming := hole_incoming layout allocated (OpenGraph.fill_replaces step) located
    apply replacement_located layout allocated (OpenGraph.fill_replaces step) _ located
    exact ⟨incoming, ordinal, inside, _, _, rfl, rfl⟩
  · rw [oldFrontier, List.map_cons, List.nodup_cons] at distinct
    simpa only [completedLeaf, OpenGraph.frontier, List.nil_append] using nextFrontier ▸ distinct.2

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_frontier_update
