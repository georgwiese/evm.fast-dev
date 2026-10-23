import InitECandidate.Solver.Mpt.WitnessCorePathInvariant
import InitECandidate.Solver.Mpt.WitnessCoreRegistryCache

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Restoring caller locals or spending a real loop tick changes none of
the actual pending or completed path bytes and allocation separations. -/
theorem ActiveRegistry.PathModel.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg : Configuration)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry target frontier db cfg)
    (paths : registry.PathModel) (validEq : next.nodes.graph.valid=registry.nodes.graph.valid)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) : next.PathModel := by
  have agree : ∀ query,registry.nodes.graph.Footprint query → target.memory query=source.memory query:=by intros; rw [memory]
  have nodes : next.nodes.PathModel:=
    ⟨paths.nodes.bytes.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be registry.nodes.graph next.nodes.graph
      validEq domain endian agree (by intros; rw [memory]),
      paths.nodes.regions.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.nodes.graph next.nodes.graph frontier cfg.heap.toNat validEq agree,
      paths.nodes.separated.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.nodes.graph next.nodes.graph validEq agree⟩
  refine ⟨nodes,?_,?_,?_,paths.pendingPending⟩
  · intro entry member
    exact (paths.pending entry member).of_fields source target entry.data.payload memory domain endian
  · intro node member active tag index inside entry inStack owner slot occupied payload offset offsetInside
    have oldMember : registry.nodes.graph.valid node:=by rwa [validEq] at member
    rw [memory] at tag inside ⊢
    exact paths.nodePending node oldMember active tag index inside entry inStack owner slot occupied payload offset offsetInside
  · intro entry inStack pointer length payload index inside owner member active offset offsetInside
    have oldMember : registry.nodes.graph.valid owner:=by rwa [validEq] at member
    rw [memory] at offsetInside
    exact paths.pendingNode entry inStack pointer length payload index inside owner oldMember active offset offsetInside

/-- Preserve the old completed registry and all old pending buffers
through a real decoder frame. Its incoming heap remains an old-allocation
bound even when the actual allocator has advanced beyond it. -/
theorem ActiveRegistry.PathModel.normal_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db limit : BitVec 64) (cfg : Configuration)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry target frontier db cfg)
    (paths : registry.PathModel) (validEq : next.nodes.graph.valid=registry.nodes.graph.valid)
    (view : View source db cfg.cursor.toNat cfg.heap.toNat cfg.stack)
    (below : cfg.cursor.toNat≤2713717616) (lower : 2713731432≤frontier)
    (frame : WitnessDecode.NormalFrame source target cfg.heap cfg.cursor limit) : next.PathModel := by
  have agree : ∀ query,registry.nodes.graph.Footprint query → target.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.nodes.graph.footprint_bounds frontier cfg.heap.toNat registry.nodes.regions query required
    exact frame.memory query (by omega) bounds.2
  have tags (node : BitVec 64) (member : registry.nodes.graph.valid node) (active : node≠0#64) :
      wordAt target.memory node=wordAt source.memory node:=by
    unfold wordAt
    rw [agree node (.header node member active)]
  have nodes:=paths.nodes.normal_frame source target frontier cfg.heap cfg.heap db cfg.cursor limit registry.nodes next.nodes
    validEq (by omega) (Nat.le_refl _) frame
  refine ⟨nodes,?_,?_,?_,paths.pendingPending⟩
  · intro entry member
    have before:=(view.before entry member).mono entry.data entry.mark cfg.heap.toNat (view.marks entry member)
    exact (paths.pending entry member).database_frame source target entry.record db cfg.heap entry.data (view.records entry member)
      before (DatabaseFrame.of_decode source target cfg.heap cfg.cursor limit frame below)
  · intro node member active tag index inside entry inStack owner slot occupied payload offset offsetInside
    have oldMember : registry.nodes.graph.valid node:=by rwa [validEq] at member
    have oldTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64:=by rwa [tags node oldMember active] at tag
    have fields:=registry.nodes.graph.path_word_agreement target.memory agree node oldMember active oldTag
    rw [fields.2] at inside
    rw [fields.1]
    exact paths.nodePending node oldMember active oldTag index inside entry inStack owner slot occupied payload offset offsetInside
  · intro entry inStack pointer length payload index inside owner member active offset offsetInside
    have oldMember : registry.nodes.graph.valid owner:=by rwa [validEq] at member
    rw [tags owner oldMember active] at offsetInside
    exact paths.pendingNode entry inStack pointer length payload index inside owner oldMember active offset offsetInside

theorem PathInvariant.dec_clock (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cfg : Configuration)
    (model : PathInvariant input frontier db limit source cfg) :
    PathInvariant input frontier db limit (decClockHOLFinite source) cfg := by
  obtain ⟨registry,paths⟩:=model.registry
  obtain ⟨next,validEq⟩:=registry.of_fields source (decClockHOLFinite source) frontier db cfg rfl rfl rfl
  exact ⟨model.base.dec_clock input frontier db limit source cfg,model.little,
    next,paths.of_fields source (decClockHOLFinite source) frontier db cfg registry next validEq rfl rfl rfl⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.normal_frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.PathInvariant.dec_clock
