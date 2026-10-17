import InitECandidate.Solver.WitnessRadix.LayoutLocated
import InitECandidate.Solver.WitnessRadix.SplitGraphFill

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open SplitScope

theorem incoming_mono (layout : Layout) (allocated next : Nat) (increase : allocated ≤ next) (word : BitVec 64)
    (incoming : Incoming layout allocated word) : Incoming layout next word := by
  obtain ⟨pool, offset, bounds, rfl⟩ := incoming
  refine ⟨pool, offset, ?_, rfl⟩
  cases pool with
  | header => exact bounds
  | keys =>
      obtain ⟨node, old, field, selected, offsetEq⟩ := bounds
      exact ⟨node, by omega, field, selected, offsetEq⟩
  | vals | primary | backup | records => exact False.elim bounds

theorem located_mono (layout : Layout) (allocated next : Nat) (increase : allocated ≤ next)
    (tree : OpenGraph.Tree) (located : Located layout allocated tree) : Located layout next tree := by
  induction tree with
  | hole slot expected => exact incoming_mono layout allocated next increase slot located
  | complete slot root tree => exact ⟨incoming_mono layout allocated next increase slot located.1, located.2⟩
  | branch slot node position zero one ihZero ihOne =>
      obtain ⟨incoming, ⟨index, bound, root⟩, zeroLocated, oneLocated⟩ := located
      exact ⟨incoming_mono layout allocated next increase slot incoming, ⟨index, by omega, root⟩,
        ihZero zeroLocated, ihOne oneLocated⟩

theorem replacement_located (layout : Layout) (allocated : Nat)
    {address : BitVec 64} {tree : Graph.Tree} {replacement before after : OpenGraph.Tree}
    (step : OpenGraph.ReplaceHole address tree replacement before after)
    (newLocated : Located layout allocated replacement) (located : Located layout allocated before) :
    Located layout allocated after := by
  induction step with
  | here => exact newLocated
  | zero step ih => exact ⟨located.1, located.2.1, ih located.2.2.1, located.2.2.2⟩
  | one step ih => exact ⟨located.1, located.2.1, located.2.2.1, ih located.2.2.2⟩

theorem hole_incoming (layout : Layout) (allocated : Nat)
    {address : BitVec 64} {tree : Graph.Tree} {replacement before after : OpenGraph.Tree}
    (step : OpenGraph.ReplaceHole address tree replacement before after) (located : Located layout allocated before) :
    Incoming layout allocated address := by
  induction step with
  | here => exact located
  | zero step ih => exact ih located.2.2.1
  | one step ih => exact ih located.2.2.2

theorem branch_located (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (zero one : Graph.Tree) :
    Located layout (allocated + 1) (SplitCount.branchReplacement context zero one) := by
  have incoming : Incoming layout allocated context.dest :=
    ⟨destination.1, destination.2, atLayout.incoming, atLayout.destEq⟩
  refine ⟨incoming_mono layout allocated (allocated + 1) (by omega) context.dest incoming,
    ⟨allocated, by omega, atLayout.nodeEq⟩, ?_, ?_⟩
  · refine ⟨.keys, 32 * layout.count + 24 * allocated + 8, ⟨allocated, by omega, 1, Or.inl rfl, rfl⟩, ?_⟩
    rw [atLayout.nodeEq]
    exact branch_address_field layout.keys layout.count allocated 1
  · refine ⟨.keys, 32 * layout.count + 24 * allocated + 16, ⟨allocated, by omega, 2, Or.inr rfl, rfl⟩, ?_⟩
    rw [atLayout.nodeEq]
    exact branch_address_field layout.keys layout.count allocated 2

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.located_mono
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.replacement_located
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.branch_located
