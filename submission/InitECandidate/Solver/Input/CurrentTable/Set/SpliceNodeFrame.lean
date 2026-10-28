import InitECandidate.Solver.Input.CurrentTable.Set.SpliceMemory

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix QueryBranch

theorem parents_node_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal index : BitVec 64)
    (geometry : New.Geometry table cap) (nodeInside : node.toNat ≤ cap.toNat) (leafInside : leaf.toNat ≤ cap.toNat)
    (internalInside : internal.toNat ≤ cap.toNat) (indexInside : index.toNat ≤ cap.toNat)
    (field : Nat) (small : field < 32) (notParent : field ≠ 0) :
    (parentsStored source (New.nodesPointer table cap) node parent leaf internal).memory (FindLeaf.cell (New.nodesPointer table cap) index field) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) index field) := by
  rw [parentsStored,node_other _ table cap node index internal 0 field geometry nodeInside indexInside (by decide) small (Or.inr notParent),
    node_other _ table cap leaf index internal 0 field geometry leafInside indexInside (by decide) small (Or.inr notParent),
    node_other _ table cap internal index parent 0 field geometry internalInside indexInside (by decide) small (Or.inr notParent)]

theorem children_node_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node leaf internal index : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (internalInside : internal.toNat ≤ cap.toNat) (indexInside : index.toNat ≤ cap.toNat)
    (field : Nat) (small : field < 32) (awayLeft : index ≠ internal ∨ field ≠ 8) (awayRight : index ≠ internal ∨ field ≠ 16) :
    (childrenStored source (New.nodesPointer table cap) node leaf internal query difference).memory (FindLeaf.cell (New.nodesPointer table cap) index field) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) index field) := by
  rw [childrenStored,node_other _ table cap internal index _ 16 field geometry internalInside indexInside (by decide) small awayRight,
    node_other _ table cap internal index _ 8 field geometry internalInside indexInside (by decide) small awayLeft]

theorem attached_node_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent internal oldLeft index : BitVec 64)
    (geometry : New.Geometry table cap) (parentInside : parent.toNat ≤ cap.toNat) (indexInside : index.toNat ≤ cap.toNat)
    (field : Nat) (small : field < 32) (awayLeft : index ≠ parent ∨ field ≠ 8) (awayRight : index ≠ parent ∨ field ≠ 16) :
    (attached source table cap node parent internal oldLeft).memory (FindLeaf.cell (New.nodesPointer table cap) index field) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) index field) := by
  unfold attached
  split
  · exact header_node source table cap internal index 56 field geometry indexInside (by decide) small
  · split
    · exact node_other source table cap parent index internal 8 field geometry parentInside indexInside (by decide) small awayLeft
    · exact node_other source table cap parent index internal 16 field geometry parentInside indexInside (by decide) small awayRight

/-- Original parent/child/root rewiring cannot change any node bit marker. -/
theorem splice_bit (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft index : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat) (indexInside : index.toNat ≤ cap.toNat) :
    (spliceResult source table cap node parent leaf internal oldLeft query difference).memory (FindLeaf.cell (New.nodesPointer table cap) index 24) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) index 24) := by
  rw [spliceResult,attached_node_field _ table cap node parent internal oldLeft index geometry parentInside indexInside 24 (by decide) (Or.inr (by decide)) (Or.inr (by decide)),
    children_node_field _ table cap node leaf internal index query difference geometry internalInside indexInside 24 (by decide) (Or.inr (by decide)) (Or.inr (by decide)),
    parents_node_field _ table cap node parent leaf internal index geometry nodeInside leafInside internalInside indexInside 24 (by decide) (by decide)]
  rfl

/-- A genuine leaf value survives all original rewiring: neither the new
internal node nor its old internal parent can be that leaf. -/
theorem splice_leaf_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft index : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat) (indexInside : index.toNat ≤ cap.toNat)
    (notInternal : index ≠ internal) (notParent : index ≠ parent) :
    (spliceResult source table cap node parent leaf internal oldLeft query difference).memory (FindLeaf.cell (New.nodesPointer table cap) index 8) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) index 8) := by
  rw [spliceResult,attached_node_field _ table cap node parent internal oldLeft index geometry parentInside indexInside 8 (by decide) (Or.inl notParent) (Or.inl notParent),
    children_node_field _ table cap node leaf internal index query difference geometry internalInside indexInside 8 (by decide) (Or.inl notInternal) (Or.inl notInternal),
    parents_node_field _ table cap node parent leaf internal index geometry nodeInside leafInside internalInside indexInside 8 (by decide) (by decide)]
  rfl

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_bit
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_leaf_value
