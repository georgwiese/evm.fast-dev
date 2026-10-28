import InitECandidate.Solver.Input.CurrentTable.Set.SpliceLocals
import InitECandidate.Solver.Input.CurrentTable.EarlierWrites

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def parentsStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node parent leaf internal : BitVec 64) :=
  putNode (putNode (putNode source base internal 0 parent) base leaf 0 internal) base node 0 internal

/-- The three original parent-pointer stores operate on the real fresh
internal node, fresh leaf and reached old subtree. -/
theorem parents_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap node parent leaf internal pointer : BitVec 64) (difference : Nat)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat)
    (locals : SpliceLocals source table (New.nodesPointer table cap) node parent leaf internal pointer difference) :
    evaluateHOLFiniteState source afterRefresh =
      evaluateHOLFiniteState (parentsStored source (New.nodesPointer table cap) node parent leaf internal) afterOldParent := by
  let base := New.nodesPointer table cap
  let one := putNode source base internal 0 parent
  let two := putNode one base leaf 0 internal
  have first := store_named_node source table cap internal parent "ni" 0 (localVar "p") domain geometry internalInside (by decide) (by decide)
    locals.nodesCell locals.internalCell (Request.local_word source "p" parent locals.parentCell)
  have second := store_named_node one table cap leaf internal "nl" 0 (localVar "ni") domain geometry leafInside (by decide) (by decide)
    locals.nodesCell locals.leafCell (Request.local_word one "ni" internal locals.internalCell)
  have third := store_named_node two table cap node internal "n" 0 (localVar "ni") domain geometry nodeInside (by decide) (by decide)
    locals.nodesCell locals.nodeCell (Request.local_word two "ni" internal locals.internalCell)
  rw [splice_shapes.2.2.2.1,evaluateHOLFiniteState_seq_line780,first]
  simp only
  rw [splice_shapes.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,second]
  simp only
  rw [splice_shapes.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,third]
  rfl

theorem parents_query (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap node parent leaf internal pointer : BitVec 64) (query : KeyBits.Key)
    (geometry : New.Geometry table cap) (nodeInside : node.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat)
    (before : pointer.toNat+32 ≤ table.toNat) (view : FirstDiff.ByteView source pointer query) :
    FirstDiff.ByteView (parentsStored source (New.nodesPointer table cap) node parent leaf internal) pointer query :=
  node_earlier_key _ table cap node internal pointer 0 query geometry nodeInside (by decide) before
    (node_earlier_key _ table cap leaf internal pointer 0 query geometry leafInside (by decide) before
      (node_earlier_key _ table cap internal parent pointer 0 query geometry internalInside (by decide) before view))

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.parents_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.parents_query
