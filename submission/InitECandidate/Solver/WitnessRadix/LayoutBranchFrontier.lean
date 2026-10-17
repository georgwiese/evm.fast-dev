import InitECandidate.Solver.WitnessRadix.LayoutFrontierSlots
import InitECandidate.Solver.WitnessRadix.OpenGraphFrontier

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open SplitScope

theorem split_located (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (zero one : Graph.Tree) (before after : OpenGraph.Tree)
    (step : OpenGraph.FillFirst context.dest (.branch context.position zero one)
      (SplitCount.branchReplacement context zero one) before after)
    (located : Located layout allocated before) : Located layout (allocated + 1) after := by
  exact replacement_located layout (allocated + 1) (OpenGraph.fill_replaces step)
    (branch_located layout context allocated depth destination atLayout zero one)
    (located_mono layout allocated (allocated + 1) (by omega) before located)

theorem split_frontier_distinct (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout) (branchRoom : allocated < layout.count)
    (zero one : Graph.Tree) (before after : OpenGraph.Tree)
    (step : OpenGraph.FillFirst context.dest (.branch context.position zero one)
      (SplitCount.branchReplacement context zero one) before after)
    (located : Located layout allocated before) (distinct : ((OpenGraph.frontier before).map Prod.fst).Nodup) :
    ((OpenGraph.frontier after).map Prod.fst).Nodup := by
  obtain ⟨pending, oldFrontier, nextFrontier⟩ := OpenGraph.fill_frontier step
  have pendingDistinct : (pending.map Prod.fst).Nodup := by
    rw [oldFrontier, List.map_cons, List.nodup_cons] at distinct
    exact distinct.2
  have newAbsent (field : Nat) (fieldBound : field < 3) :
      context.node + BitVec.ofNat 64 (8 * field) ∉ pending.map Prod.fst := by
    intro member
    obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
    have oldMember : entry ∈ OpenGraph.frontier before := by
      rw [oldFrontier]
      exact List.mem_cons_of_mem _ entryMember
    exact fresh_frontier_slot layout valid allocated branchRoom before located entry oldMember field fieldBound
      (same.trans (context_node_cell layout context allocated depth destination atLayout field))
  have childrenNe : context.node + 8#64 ≠ context.node + 16#64 := by
    intro same
    have left := context_node_cell layout context allocated depth destination atLayout 1
    have right := context_node_cell layout context allocated depth destination atLayout 2
    exact branch_fields_ne layout valid allocated branchRoom 1 2 (by decide) (by decide) (by decide)
      (left.symm.trans (same.trans right))
  rw [nextFrontier]
  change ((context.node + 8#64) :: (context.node + 16#64) :: pending.map Prod.fst).Nodup
  apply List.nodup_cons.mpr
  refine ⟨?_, List.nodup_cons.mpr ⟨newAbsent 2 (by decide), pendingDistinct⟩⟩
  intro member
  rcases List.mem_cons.mp member with same | tail
  · exact childrenNe same
  · exact newAbsent 1 (by decide) tail

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_located
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_frontier_distinct
