import InitECandidate.Solver.Mpt.WitnessNodeRegistryPathModel
import InitECandidate.Solver.Mpt.WitnessRecordPathBytes

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Full actual path bytes for both completed nodes and live extension
records. Separation covers pending branches as well as completed nodes,
since the original materializer writes branch children before registration. -/
structure ActiveRegistry.PathModel {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frontier : Nat} {db : BitVec 64} {cfg : Configuration}
    (registry : ActiveRegistry source frontier db cfg) : Prop where
  nodes : registry.nodes.PathModel
  pending : ∀ entry∈cfg.stack,entry.data.payload.PathBytes source
  nodePending : ∀ node,registry.nodes.graph.valid node → node≠0#64 →
    (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
    ∀ index<(wordAt source.memory (node+40#64)).toNat,
    ∀ entry∈cfg.stack,∀ owner slot occupied,entry.data.payload=.branch owner slot occupied → ∀ offset<176,
      panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)≠byteAddress owner offset
  pendingNode : ∀ entry∈cfg.stack,∀ pointer length,entry.data.payload=.extension pointer length →
    ∀ index<length.toNat,∀ owner,registry.nodes.graph.valid owner → owner≠0#64 →
    ∀ offset<TrieWalk.nodeBytes (wordAt source.memory owner),
      panByteAlignHOL (width:=64) (byteAddress pointer index)≠byteAddress owner offset
  pendingPending : ∀ entry∈cfg.stack,∀ pointer length,entry.data.payload=.extension pointer length →
    ∀ index<length.toNat,∀ other∈cfg.stack,∀ owner slot occupied,other.data.payload=.branch owner slot occupied →
    ∀ offset<176,panByteAlignHOL (width:=64) (byteAddress pointer index)≠byteAddress owner offset

/-- The existing physical/rank invariant, the same actual completed and
pending registry, and the real little-endian entry fact. -/
structure PathInvariant (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cfg : Configuration) : Prop where
  base : Invariant input frontier db limit source cfg
  little : source.be=false
  registry : ∃ current : ActiveRegistry source frontier db cfg,current.PathModel

theorem PathInvariant.rich (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cfg : Configuration)
    (model : PathInvariant input frontier db limit source cfg) : RichInvariant input frontier db limit source cfg := by
  obtain ⟨registry,paths⟩:=model.registry
  exact ⟨model.base,⟨registry⟩⟩

/-- The real empty-stack decoder starts with no pending or completed
paths. No input graph, byte-range, or future callee success is assumed. -/
theorem PathInvariant.initial (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base : Invariant input frontier db limit source ⟨heap,cursor,[],.decode,true⟩) (little : source.be=false) :
    PathInvariant input frontier db limit source ⟨heap,cursor,[],.decode,true⟩ := by
  let registry : ActiveRegistry source frontier db ⟨heap,cursor,[],.decode,true⟩:=
    ⟨NodeRegistry.empty source frontier heap db,ChildViews.empty source _,
      (by intro entry member; cases member),
      (by intro phase; cases phase)⟩
  refine ⟨base,little,registry,NodeRegistry.PathModel.empty source frontier heap db,?_,?_,?_,?_⟩
  all_goals intros; simp_all only [List.not_mem_nil]

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.PathInvariant.rich
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.PathInvariant.initial
