import InitECandidate.Solver.Input.CurrentTable.Set.SpliceMemory

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix QueryBranch

theorem parents_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal keyNode : BitVec 64) (key : KeyBits.Key)
    (geometry : New.Geometry table cap) (nodeInside : node.toNat ≤ cap.toNat) (leafInside : leaf.toNat ≤ cap.toNat)
    (internalInside : internal.toNat ≤ cap.toNat) (keyInside : keyNode.toNat ≤ cap.toNat)
    (view : FirstDiff.ByteView source (slot (New.keysPointer table) keyNode 32) key) :
    FirstDiff.ByteView (parentsStored source (New.nodesPointer table cap) node parent leaf internal) (slot (New.keysPointer table) keyNode 32) key :=
  node_key _ table cap node keyNode internal 0 key geometry nodeInside keyInside (by decide)
    (node_key _ table cap leaf keyNode internal 0 key geometry leafInside keyInside (by decide)
      (node_key _ table cap internal keyNode parent 0 key geometry internalInside keyInside (by decide) view))

theorem children_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node leaf internal keyNode : BitVec 64)
    (query key : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (internalInside : internal.toNat ≤ cap.toNat) (keyInside : keyNode.toNat ≤ cap.toNat)
    (view : FirstDiff.ByteView source (slot (New.keysPointer table) keyNode 32) key) :
    FirstDiff.ByteView (childrenStored source (New.nodesPointer table cap) node leaf internal query difference) (slot (New.keysPointer table) keyNode 32) key :=
  node_key _ table cap internal keyNode _ 16 key geometry internalInside keyInside (by decide)
    (node_key _ table cap internal keyNode _ 8 key geometry internalInside keyInside (by decide) view)

theorem attached_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent internal oldLeft keyNode : BitVec 64)
    (key : KeyBits.Key) (geometry : New.Geometry table cap) (parentInside : parent.toNat ≤ cap.toNat) (keyInside : keyNode.toNat ≤ cap.toNat)
    (view : FirstDiff.ByteView source (slot (New.keysPointer table) keyNode 32) key) :
    FirstDiff.ByteView (attached source table cap node parent internal oldLeft) (slot (New.keysPointer table) keyNode 32) key := by
  unfold attached
  split
  · exact header_key source table cap internal keyNode 56 key geometry keyInside (by decide) view
  · split
    · exact node_key source table cap parent keyNode internal 8 key geometry parentInside keyInside (by decide) view
    · exact node_key source table cap parent keyNode internal 16 key geometry parentInside keyInside (by decide) view

/-- Every original rewiring store preserves all physical key-array bytes. -/
theorem splice_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft keyNode : BitVec 64)
    (query key : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat) (keyInside : keyNode.toNat ≤ cap.toNat)
    (view : FirstDiff.ByteView source (slot (New.keysPointer table) keyNode 32) key) :
    FirstDiff.ByteView (spliceResult source table cap node parent leaf internal oldLeft query difference) (slot (New.keysPointer table) keyNode 32) key :=
  attached_key _ table cap node parent internal oldLeft keyNode key geometry parentInside keyInside
    (children_key _ table cap node leaf internal keyNode query key difference geometry internalInside keyInside
      (parents_key (bind source "nodes" (New.nodesPointer table cap)) table cap node parent leaf internal keyNode key geometry nodeInside leafInside internalInside keyInside (view.of_frame rfl)))

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_key
