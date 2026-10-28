import InitECandidate.Solver.Input.CurrentTable.Set.SpliceNodeFrame

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix QueryBranch

def childPhase (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal : BitVec 64) (query : KeyBits.Key) (difference : Nat) :=
  childrenStored (parentsStored (bind source "nodes" (New.nodesPointer table cap)) (New.nodesPointer table cap) node parent leaf internal)
    (New.nodesPointer table cap) node leaf internal query difference

theorem child_phase_old (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal index : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat)
    (indexInside : index.toNat ≤ cap.toNat) (different : index ≠ internal) (field : Nat) (small : field < 32) (notParent : field ≠ 0) :
    (childPhase source table cap node parent leaf internal query difference).memory (FindLeaf.cell (New.nodesPointer table cap) index field) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) index field) := by
  rw [childPhase,children_node_field _ table cap node leaf internal index query difference geometry internalInside indexInside field small (Or.inl different) (Or.inl different),
    parents_node_field _ table cap node parent leaf internal index geometry nodeInside leafInside internalInside indexInside field small notParent]
  rfl

theorem children_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node leaf internal : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap) (inside : internal.toNat ≤ cap.toNat) :
    (childrenStored source (New.nodesPointer table cap) node leaf internal query difference).memory (FindLeaf.cell (New.nodesPointer table cap) internal 8) =
      .word (if KeyBits.bit query difference then node else leaf) ∧
    (childrenStored source (New.nodesPointer table cap) node leaf internal query difference).memory (FindLeaf.cell (New.nodesPointer table cap) internal 16) =
      .word (if KeyBits.bit query difference then leaf else node) := by
  constructor
  · rw [childrenStored,node_other _ table cap internal internal _ 16 8 geometry inside inside (by decide) (by decide) (Or.inr (by decide))]
    simp [putNode,StoreWord.put]
  · simp [childrenStored,putNode,StoreWord.put]

theorem splice_new_children (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap) (parentInside : parent.toNat ≤ cap.toNat)
    (internalInside : internal.toNat ≤ cap.toNat) (different : internal ≠ parent) :
    (spliceResult source table cap node parent leaf internal oldLeft query difference).memory (FindLeaf.cell (New.nodesPointer table cap) internal 8) =
      .word (if KeyBits.bit query difference then node else leaf) ∧
    (spliceResult source table cap node parent leaf internal oldLeft query difference).memory (FindLeaf.cell (New.nodesPointer table cap) internal 16) =
      .word (if KeyBits.bit query difference then leaf else node) := by
  constructor
  · rw [spliceResult,attached_node_field _ table cap node parent internal oldLeft internal geometry parentInside internalInside 8 (by decide) (Or.inl different) (Or.inl different)]
    exact (children_cells _ table cap node leaf internal query difference geometry internalInside).1
  · rw [spliceResult,attached_node_field _ table cap node parent internal oldLeft internal geometry parentInside internalInside 16 (by decide) (Or.inl different) (Or.inl different)]
    exact (children_cells _ table cap node leaf internal query difference geometry internalInside).2

/-- For any old node, the left child changes only at the selected old
parent when the original real left-cell comparison succeeds. -/
theorem splice_old_left (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft index : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat)
    (indexInside : index.toNat ≤ cap.toNat) (different : index ≠ internal) :
    (spliceResult source table cap node parent leaf internal oldLeft query difference).memory (FindLeaf.cell (New.nodesPointer table cap) index 8) =
      if parent ≠ 0#64 ∧ index = parent ∧ oldLeft = node then .word internal else source.memory (FindLeaf.cell (New.nodesPointer table cap) index 8) := by
  let state := childPhase source table cap node parent leaf internal query difference
  change (attached state table cap node parent internal oldLeft).memory _ = _
  have kept := child_phase_old source table cap node parent leaf internal index query difference geometry nodeInside leafInside internalInside indexInside different 8 (by decide) (by decide)
  by_cases zero : parent = 0#64
  · rw [attached,if_pos zero,header_node _ table cap internal index 56 8 geometry indexInside (by decide) (by decide)]
    rw [if_neg (show ¬(parent ≠ 0#64 ∧ index = parent ∧ oldLeft = node) from fun condition => condition.1 zero)]
    exact kept
  · rw [attached,if_neg zero]
    by_cases selected : oldLeft = node
    · rw [if_pos selected]
      by_cases same : index = parent
      · subst index
        simp [putNode,StoreWord.put,zero,selected]
      · rw [node_other _ table cap parent index internal 8 8 geometry parentInside indexInside (by decide) (by decide) (Or.inl same)]
        simpa only [same,false_and,and_false,if_false] using kept
    · rw [if_neg selected,node_other _ table cap parent index internal 16 8 geometry parentInside indexInside (by decide) (by decide) (Or.inr (by decide))]
      simpa only [selected,and_false,if_false] using kept

theorem splice_old_right (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft index : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat)
    (indexInside : index.toNat ≤ cap.toNat) (different : index ≠ internal) :
    (spliceResult source table cap node parent leaf internal oldLeft query difference).memory (FindLeaf.cell (New.nodesPointer table cap) index 16) =
      if parent ≠ 0#64 ∧ index = parent ∧ oldLeft ≠ node then .word internal else source.memory (FindLeaf.cell (New.nodesPointer table cap) index 16) := by
  let state := childPhase source table cap node parent leaf internal query difference
  change (attached state table cap node parent internal oldLeft).memory _ = _
  have kept := child_phase_old source table cap node parent leaf internal index query difference geometry nodeInside leafInside internalInside indexInside different 16 (by decide) (by decide)
  by_cases zero : parent = 0#64
  · rw [attached,if_pos zero,header_node _ table cap internal index 56 16 geometry indexInside (by decide) (by decide)]
    rw [if_neg (show ¬(parent ≠ 0#64 ∧ index = parent ∧ oldLeft ≠ node) from fun condition => condition.1 zero)]
    exact kept
  · rw [attached,if_neg zero]
    by_cases selected : oldLeft = node
    · rw [if_pos selected,node_other _ table cap parent index internal 8 16 geometry parentInside indexInside (by decide) (by decide) (Or.inr (by decide))]
      simpa only [selected,ne_eq,not_true_eq_false,and_false,if_false] using kept
    · rw [if_neg selected]
      by_cases same : index = parent
      · subst index
        simp [putNode,StoreWord.put,zero,selected]
      · rw [node_other _ table cap parent index internal 16 16 geometry parentInside indexInside (by decide) (by decide) (Or.inl same)]
        simpa only [same,false_and,and_false,if_false] using kept

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_new_children
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_old_left
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_old_right
