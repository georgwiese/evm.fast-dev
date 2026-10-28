import InitECandidate.Solver.Input.CurrentTable.Set.SpliceParents
import InitECandidate.Solver.Input.CurrentTable.Set.SpliceChildren

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

private theorem node_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node value : BitVec 64) (offset : Nat) :
    (putNode source base node offset value).locals = source.locals := rfl

theorem SpliceLocals.of_locals {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base node parent leaf internal pointer : BitVec 64} {difference : Nat}
    (locals : SpliceLocals source table base node parent leaf internal pointer difference) (same : target.locals = source.locals) :
    SpliceLocals target table base node parent leaf internal pointer difference := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> rw [same]
  · exact locals.tableCell
  · exact locals.nodesCell
  · exact locals.nodeCell
  · exact locals.parentCell
  · exact locals.leafCell
  · exact locals.internalCell
  · exact locals.keyCell
  · exact locals.differenceCell

theorem parents_local_map (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node parent leaf internal : BitVec 64) :
    (parentsStored source base node parent leaf internal).locals = source.locals := by
  simp only [parentsStored,node_locals]

theorem children_local_map (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node leaf internal : BitVec 64) (query : KeyBits.Key) (difference : Nat) :
    (childrenStored source base node leaf internal query difference).locals = source.locals := by
  simp only [childrenStored,node_locals]

theorem parents_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node parent leaf internal : BitVec 64) :
    MemoryMetadata.erase (parentsStored source base node parent leaf internal) = MemoryMetadata.erase source := by
  simp only [parentsStored,node_metadata]

theorem children_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node leaf internal : BitVec 64) (query : KeyBits.Key) (difference : Nat) :
    MemoryMetadata.erase (childrenStored source base node leaf internal query difference) = MemoryMetadata.erase source := by
  simp only [childrenStored,node_metadata]

theorem parents_left (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal : BitVec 64)
    (geometry : New.Geometry table cap) (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat) :
    (parentsStored source (New.nodesPointer table cap) node parent leaf internal).memory (FindLeaf.cell (New.nodesPointer table cap) parent 8) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) parent 8) := by
  rw [parentsStored,node_other _ table cap node parent internal 0 8 geometry nodeInside parentInside (by decide) (by decide) (Or.inr (by decide)),
    node_other _ table cap leaf parent internal 0 8 geometry leafInside parentInside (by decide) (by decide) (Or.inr (by decide)),
    node_other _ table cap internal parent parent 0 8 geometry internalInside parentInside (by decide) (by decide) (Or.inr (by decide))]

theorem children_left (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal : BitVec 64) (query : KeyBits.Key) (difference : Nat)
    (geometry : New.Geometry table cap) (parentInside : parent.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat)
    (different : parent ≠ internal) :
    (childrenStored source (New.nodesPointer table cap) node leaf internal query difference).memory (FindLeaf.cell (New.nodesPointer table cap) parent 8) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) parent 8) := by
  rw [childrenStored,node_other _ table cap internal parent _ 16 8 geometry internalInside parentInside (by decide) (by decide) (Or.inr (by decide)),
    node_other _ table cap internal parent _ 8 8 geometry internalInside parentInside (by decide) (by decide) (Or.inl different)]

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.parents_left
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.children_left
