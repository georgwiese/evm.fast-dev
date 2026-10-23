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
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.PathInvariant.dec_clock
