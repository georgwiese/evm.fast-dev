import InitECandidate.Solver.Input.CurrentTable.Set.SpliceAttach
import InitECandidate.Solver.Input.CurrentTable.Set.SpliceFrames
import InitECandidate.Solver.Input.CurrentTable.NewNode.Program

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def spliceResult (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) :=
  attached (childrenStored (parentsStored (bind source "nodes" (New.nodesPointer table cap)) (New.nodesPointer table cap) node parent leaf internal)
    (New.nodesPointer table cap) node leaf internal query difference) table cap node parent internal oldLeft

theorem after_split_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap node parent leaf internal pointer oldLeft : BitVec 64) (difference : Nat)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.Geometry table cap) (aligned : table.toNat%8 = 0)
    (parentInside : parent.toNat ≤ cap.toNat)
    (locals : SpliceLocals source table (New.nodesPointer table cap) node parent leaf internal pointer difference)
    (leftCell : parent ≠ 0#64 → source.memory (FindLeaf.cell (New.nodesPointer table cap) parent 8) = .word oldLeft) :
    evaluateHOLFiniteState source afterSplit =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (attached source table cap node parent internal oldLeft)) := by
  rw [splice_shapes.2.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,
    attach_execute source table cap node parent leaf internal pointer oldLeft difference domain geometry aligned parentInside locals leftCell]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- The unchanged entire post-constructor splice really performs its
refresh, parent stores, actual key-bit child stores and root/parent attach,
then returns zero, without spending any source body clock. -/
theorem splice_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap node parent leaf internal pointer oldLeft : BitVec 64) (difference : Nat) (query : KeyBits.Key)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.Geometry table cap) (aligned : table.toNat%8 = 0)
    (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat) (different : parent ≠ internal)
    (locals : SpliceLocals source table (New.nodesPointer table cap) node parent leaf internal pointer difference)
    (nodesCell : source.memory (table+40#64) = .word (New.nodesPointer table cap))
    (leftCell : parent ≠ 0#64 → source.memory (FindLeaf.cell (New.nodesPointer table cap) parent 8) = .word oldLeft)
    (inside : difference < 256) (before : pointer.toNat+32 ≤ table.toNat) (view : FirstDiff.ByteView source pointer query) :
    evaluateHOLFiniteState source splice =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (spliceResult source table cap node parent leaf internal oldLeft query difference)) := by
  let base := New.nodesPointer table cap
  let start := bind source "nodes" base
  let parentState := parentsStored start base node parent leaf internal
  let childState := childrenStored parentState base node leaf internal query difference
  have headerRead := NewNode.field_read source table base 40 domain geometry.table aligned (by decide) (by decide) locals.tableCell nodesCell
  change eval source (.load .one (.op .add [localVar "t",.const 40#64])) = _ at headerRead
  have refreshed := StateSteps.assign_execute source "nodes" _ base base locals.nodesCell headerRead
  have startLocals : SpliceLocals start table base node parent leaf internal pointer difference := locals.with_nodes
  have parentLocals : SpliceLocals parentState table base node parent leaf internal pointer difference :=
    startLocals.of_locals (parents_local_map start base node parent leaf internal)
  have parentDomain : parentState.memaddrs = InitE.ordinaryDomain := (MemoryMetadata.domain (parents_metadata start base node parent leaf internal)).trans domain
  have parentView : FirstDiff.ByteView parentState pointer query :=
    parents_query start table cap node parent leaf internal pointer query geometry nodeInside leafInside internalInside before (view.of_frame rfl)
  have splitRun := split_children_execute parentState table cap node parent leaf internal pointer difference query parentDomain geometry internalInside parentLocals inside parentView
  have childLocals : SpliceLocals childState table base node parent leaf internal pointer difference :=
    parentLocals.of_locals (children_local_map parentState base node leaf internal query difference)
  have childDomain : childState.memaddrs = InitE.ordinaryDomain :=
    (MemoryMetadata.domain (children_metadata parentState base node leaf internal query difference)).trans parentDomain
  have childLeft : parent ≠ 0#64 → childState.memory (FindLeaf.cell base parent 8) = .word oldLeft := by
    intro nonzero
    change (childrenStored parentState base node leaf internal query difference).memory _ = _
    rw [children_left parentState table cap node parent leaf internal query difference geometry parentInside internalInside different,
      parents_left start table cap node parent leaf internal geometry nodeInside parentInside leafInside internalInside]
    exact leftCell nonzero
  have finish := after_split_execute childState table cap node parent leaf internal pointer oldLeft difference childDomain geometry aligned parentInside childLocals childLeft
  rw [splice_shapes.2.2.1,evaluateHOLFiniteState_seq_line780,refreshed]
  simp only
  rw [parents_execute start table cap node parent leaf internal pointer difference domain geometry nodeInside leafInside internalInside startLocals]
  rw [splice_shapes.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,splitRun]
  exact finish

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.after_split_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_execute
