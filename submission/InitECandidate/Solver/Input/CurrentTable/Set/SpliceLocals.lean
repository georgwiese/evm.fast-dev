import InitECandidate.Solver.Input.CurrentTable.Set.SpliceProgram
import InitECandidate.Solver.Input.CurrentTable.NodeStores
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

structure SpliceLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table base node parent leaf internal pointer : BitVec 64) (difference : Nat) : Prop where
  tableCell : source.locals.lookup (ofString "t") = some (.val (.word table))
  nodesCell : source.locals.lookup (ofString "nodes") = some (.val (.word base))
  nodeCell : source.locals.lookup (ofString "n") = some (.val (.word node))
  parentCell : source.locals.lookup (ofString "p") = some (.val (.word parent))
  leafCell : source.locals.lookup (ofString "nl") = some (.val (.word leaf))
  internalCell : source.locals.lookup (ofString "ni") = some (.val (.word internal))
  keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer))
  differenceCell : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference)))

theorem SpliceLocals.with_memory {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base node parent leaf internal pointer : BitVec 64} {difference : Nat}
    (locals : SpliceLocals source table base node parent leaf internal pointer difference) (memory : BitVec 64 → HolWordLab 64) :
    SpliceLocals {source with memory := memory} table base node parent leaf internal pointer difference :=
  ⟨locals.tableCell,locals.nodesCell,locals.nodeCell,locals.parentCell,locals.leafCell,locals.internalCell,locals.keyCell,locals.differenceCell⟩

theorem SpliceLocals.with_nodes {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base node parent leaf internal pointer : BitVec 64} {difference : Nat}
    (locals : SpliceLocals source table base node parent leaf internal pointer difference) :
    SpliceLocals (bind source "nodes" base) table base node parent leaf internal pointer difference :=
  ⟨(bind_lookup_other _ "nodes" "t" base (by decide)).trans locals.tableCell,bind_lookup_same _ _ _,
    (bind_lookup_other _ "nodes" "n" base (by decide)).trans locals.nodeCell,
    (bind_lookup_other _ "nodes" "p" base (by decide)).trans locals.parentCell,
    (bind_lookup_other _ "nodes" "nl" base (by decide)).trans locals.leafCell,
    (bind_lookup_other _ "nodes" "ni" base (by decide)).trans locals.internalCell,
    (bind_lookup_other _ "nodes" "key" base (by decide)).trans locals.keyCell,
    (bind_lookup_other _ "nodes" "d" base (by decide)).trans locals.differenceCell⟩

theorem SpliceLocals.from_scoped (source leafTarget internalTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table base node parent leaf internal pointer : BitVec 64) (difference : Nat)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (nodesCell : source.locals.lookup (ofString "nodes") = some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n") = some (.val (.word node)))
    (parentCell : source.locals.lookup (ofString "p") = some (.val (.word parent)))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (differenceCell : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference)))) :
    SpliceLocals (CallNormal.continuationEntry (CallNormal.continuationEntry source leafTarget "nl" (.val (.word leaf)))
      internalTarget "ni" (.val (.word internal))) table base node parent leaf internal pointer difference := by
  let first := CallNormal.continuationEntry source leafTarget "nl" (.val (.word leaf))
  have kept (name : String) (notLeaf : ofString "nl" ≠ ofString name) (notInternal : ofString "ni" ≠ ofString name) :=
    (CallNormal.continuation_lookup_other first internalTarget "ni" name (.val (.word internal)) notInternal).trans
      (CallNormal.continuation_lookup_other source leafTarget "nl" name (.val (.word leaf)) notLeaf)
  exact ⟨(kept "t" (by decide) (by decide)).trans tableCell,(kept "nodes" (by decide) (by decide)).trans nodesCell,
    (kept "n" (by decide) (by decide)).trans nodeCell,(kept "p" (by decide) (by decide)).trans parentCell,
    (CallNormal.continuation_lookup_other first internalTarget "ni" "nl" (.val (.word internal)) (by decide)).trans
      (CallNormal.continuation_lookup_same source leafTarget "nl" (.val (.word leaf))),
    CallNormal.continuation_lookup_same first internalTarget "ni" (.val (.word internal)),
    (kept "key" (by decide) (by decide)).trans keyCell,(kept "d" (by decide) (by decide)).trans differenceCell⟩

theorem named_node_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node : BitVec 64) (name : String) (offset : Nat)
    (baseCell : source.locals.lookup (ofString "nodes") = some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString name) = some (.val (.word node))) :
    eval source (nodeFor name offset) = some (.val (.word (FindLeaf.cell base node offset))) := by
  simp [eval,nodeFor,evalHOLExact,evalListHOLExact,localVar,baseCell,nodeCell,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,FindLeaf.cell,BitVec.add_assoc]

theorem store_named_node (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node value : BitVec 64)
    (name : String) (offset : Nat) (expression : ExpHOL 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.Geometry table cap)
    (inside : node.toNat ≤ cap.toNat) (small : offset < 32) (aligned : offset%8 = 0)
    (baseCell : source.locals.lookup (ofString "nodes") = some (.val (.word (New.nodesPointer table cap))))
    (nodeCell : source.locals.lookup (ofString name) = some (.val (.word node)))
    (read : eval source expression = some (.val (.word value))) :
    evaluateHOLFiniteState source (.store (nodeFor name offset) expression) = (none,putNode source (New.nodesPointer table cap) node offset value) := by
  exact StoreWord.execute source _ _ _ _ (named_node_read source _ node name offset baseCell nodeCell) read
    (AllocatedBytes.word_mapped source (slot (New.nodesPointer table cap) node 32) 32 offset domain (geometry.node_slot node inside) small
      (slot_aligned _ node cap 32 geometry.nodes inside geometry.nodesAligned (by decide)) aligned)

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.named_node_read
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.store_named_node
