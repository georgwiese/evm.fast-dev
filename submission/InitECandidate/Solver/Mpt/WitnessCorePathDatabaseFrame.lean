import InitECandidate.Solver.Mpt.WitnessCorePathFrame
import InitECandidate.Solver.Mpt.WitnessNodeRegistryResolvePaths

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The actual resolver band retains all old completed and pending paths. -/
theorem ActiveRegistry.PathModel.database_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg : Configuration)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry target frontier db cfg)
    (paths : registry.PathModel) (validEq : next.nodes.graph.valid=registry.nodes.graph.valid)
    (view : View source db cfg.cursor.toNat cfg.heap.toNat cfg.stack)
    (lower : 2713731432≤frontier)
    (frame : DatabaseFrame source target cfg.heap) : next.PathModel := by
  have agree : ∀ query,registry.nodes.graph.Footprint query → target.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.nodes.graph.footprint_bounds frontier cfg.heap.toNat registry.nodes.regions query required
    exact frame.memory query (by omega) bounds.2
  have tags (node : BitVec 64) (member : registry.nodes.graph.valid node) (active : node≠0#64) :
      wordAt target.memory node=wordAt source.memory node:=by
    unfold wordAt
    rw [agree node (.header node member active)]
  have nodes:=paths.nodes.database_frame source target frontier cfg.heap db registry.nodes next.nodes
    validEq (by omega) frame
  refine ⟨nodes,?_,?_,?_,paths.pendingPending⟩
  · intro entry member
    have before:=(view.before entry member).mono entry.data entry.mark cfg.heap.toNat (view.marks entry member)
    exact (paths.pending entry member).database_frame source target entry.record db cfg.heap entry.data (view.records entry member)
      before frame
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

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.database_frame
