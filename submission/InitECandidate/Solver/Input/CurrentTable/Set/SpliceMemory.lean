import InitECandidate.Solver.Input.CurrentTable.Set.SpliceExecute

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix QueryBranch

private theorem refresh_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    (bind source "nodes" base).memory = source.memory := rfl
private theorem refresh_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    MemoryMetadata.erase (bind source "nodes" base) = MemoryMetadata.erase source := rfl

theorem attached_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent internal oldLeft : BitVec 64) :
    MemoryMetadata.erase (attached source table cap node parent internal oldLeft) = MemoryMetadata.erase source := by
  unfold attached
  split
  · exact header_metadata _ _ _ _
  · split <;> exact node_metadata _ _ _ _ _

theorem splice_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) :
    MemoryMetadata.erase (spliceResult source table cap node parent leaf internal oldLeft query difference) = MemoryMetadata.erase source := by
  rw [spliceResult,attached_metadata,children_metadata,parents_metadata,refresh_metadata]

theorem parents_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal : BitVec 64)
    (geometry : New.Geometry table cap) (nodeInside : node.toNat ≤ cap.toNat) (leafInside : leaf.toNat ≤ cap.toNat)
    (internalInside : internal.toNat ≤ cap.toNat) (field : Nat) (small : field < 88) :
    (parentsStored source (New.nodesPointer table cap) node parent leaf internal).memory (table+BitVec.ofNat 64 field) =
      source.memory (table+BitVec.ofNat 64 field) := by
  rw [parentsStored,node_header _ table cap node internal 0 field geometry nodeInside (by decide) small,
    node_header _ table cap leaf internal 0 field geometry leafInside (by decide) small,
    node_header _ table cap internal parent 0 field geometry internalInside (by decide) small]

theorem children_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node leaf internal : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap) (internalInside : internal.toNat ≤ cap.toNat)
    (field : Nat) (small : field < 88) :
    (childrenStored source (New.nodesPointer table cap) node leaf internal query difference).memory (table+BitVec.ofNat 64 field) =
      source.memory (table+BitVec.ofNat 64 field) := by
  rw [childrenStored,node_header _ table cap internal _ 16 field geometry internalInside (by decide) small,
    node_header _ table cap internal _ 8 field geometry internalInside (by decide) small]

theorem attached_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent internal oldLeft : BitVec 64)
    (geometry : New.Geometry table cap) (parentInside : parent.toNat ≤ cap.toNat) (field : Nat) (small : field < 88) (notRoot : field ≠ 56) :
    (attached source table cap node parent internal oldLeft).memory (table+BitVec.ofNat 64 field) = source.memory (table+BitVec.ofNat 64 field) := by
  unfold attached
  split
  · exact header_other source table internal 56 field geometry.table (by decide) small notRoot
  · split
    · exact node_header source table cap parent internal 8 field geometry parentInside (by decide) small
    · exact node_header source table cap parent internal 16 field geometry parentInside (by decide) small

/-- Original rewiring preserves every metadata field except the root. -/
theorem splice_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat)
    (field : Nat) (small : field < 88) (notRoot : field ≠ 56) :
    (spliceResult source table cap node parent leaf internal oldLeft query difference).memory (table+BitVec.ofNat 64 field) =
      source.memory (table+BitVec.ofNat 64 field) := by
  rw [spliceResult,attached_header _ table cap node parent internal oldLeft geometry parentInside field small notRoot,
    children_header _ table cap node leaf internal query difference geometry internalInside field small,
    parents_header _ table cap node parent leaf internal geometry nodeInside leafInside internalInside field small,refresh_memory]

theorem splice_root (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat) :
    (spliceResult source table cap node parent leaf internal oldLeft query difference).memory (table+56#64) =
      if parent = 0#64 then .word internal else source.memory (table+56#64) := by
  by_cases zero : parent = 0#64
  · simp [spliceResult,attached,zero,New.putField,StoreWord.put]
  · rw [spliceResult,attached,if_neg zero]
    have unchanged (offset : Nat) (small : offset < 32) :
        (putNode (childrenStored (parentsStored (bind source "nodes" (New.nodesPointer table cap)) (New.nodesPointer table cap) node parent leaf internal)
          (New.nodesPointer table cap) node leaf internal query difference) (New.nodesPointer table cap) parent offset internal).memory (table+56#64) = source.memory (table+56#64) := by
      rw [node_header _ table cap parent internal offset 56 geometry parentInside small (by decide),
        children_header _ table cap node leaf internal query difference geometry internalInside 56 (by decide),
        parents_header _ table cap node parent leaf internal geometry nodeInside leafInside internalInside 56 (by decide),refresh_memory]
    split
    · exact unchanged 8 (by decide)
    · exact unchanged 16 (by decide)

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_metadata
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_header
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_root
