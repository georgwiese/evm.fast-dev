import InitECandidate.Solver.WitnessRadix.LayoutLocationStep
import InitECandidate.Solver.WitnessRadix.LayoutProtected

namespace InitECandidate.Solver.WitnessRadix.BackingLayout

theorem frontier_incoming (layout : Layout) (allocated : Nat) (tree : OpenGraph.Tree) (located : Located layout allocated tree)
    (entry : BitVec 64 × Graph.Tree) (member : entry ∈ OpenGraph.frontier tree) : Incoming layout allocated entry.1 := by
  induction tree with
  | hole slot expected =>
      have same : entry = (slot, expected) := List.mem_singleton.mp member
      subst entry
      exact located
  | complete slot root tree => simp [OpenGraph.frontier] at member
  | branch slot node position zero one ihZero ihOne =>
      rcases List.mem_append.mp member with zeroMember | oneMember
      · exact ihZero located.2.2.1 zeroMember
      · exact ihOne located.2.2.2 oneMember

theorem branch_fields_ne (layout : Layout) (valid : Valid layout) (allocated : Nat) (inside : allocated < layout.count)
    (left right : Nat) (leftBound : left < 3) (rightBound : right < 3) (different : left ≠ right) :
    cell layout .keys (32 * layout.count + 24 * allocated + 8 * left) ≠
      cell layout .keys (32 * layout.count + 24 * allocated + 8 * right) :=
  branch_cells_injective layout.keys layout.count layout.capacity allocated allocated left right valid.room inside inside
    leftBound rightBound (Or.inr different) (valid.noWrap .keys)

theorem context_node_cell (layout : Layout) (context : SplitScope.SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (field : Nat) :
    context.node + BitVec.ofNat 64 (8 * field) = cell layout .keys (32 * layout.count + 24 * allocated + 8 * field) := by
  rw [atLayout.nodeEq]
  exact branch_address_field layout.keys layout.count allocated field

/-- Both newly allocated child slots are disjoint from every old frontier
slot, and from the new branch's bit word and each other. -/
theorem fresh_frontier_slot (layout : Layout) (valid : Valid layout) (allocated : Nat) (inside : allocated < layout.count)
    (tree : OpenGraph.Tree) (located : Located layout allocated tree) (entry : BitVec 64 × Graph.Tree)
    (member : entry ∈ OpenGraph.frontier tree) (field : Nat) (fieldBound : field < 3) :
    entry.1 ≠ cell layout .keys (32 * layout.count + 24 * allocated + 8 * field) := by
  exact protected_fresh layout valid allocated inside entry.1
    (incoming_protected layout allocated entry.1 (frontier_incoming layout allocated tree located entry member)) field fieldBound

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.frontier_incoming
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.fresh_frontier_slot
