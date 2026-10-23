import InitECandidate.Solver.Mpt.WitnessCorePathInvariant

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Once actual completed/pending bytes have been framed, agreement on
the real structural words transports all cross-allocation separations. -/
theorem ActiveRegistry.PathModel.of_agreement (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg : Configuration)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry target frontier db cfg)
    (paths : registry.PathModel) (nextPaths : next.nodes.PathModel) (validEq : next.nodes.graph.valid=registry.nodes.graph.valid)
    (agree : ∀ query,registry.nodes.graph.Footprint query → target.memory query=source.memory query)
    (pending : ∀ entry∈cfg.stack,entry.data.payload.PathBytes target) : next.PathModel := by
  have tags (node : BitVec 64) (member : registry.nodes.graph.valid node) (active : node≠0#64) :
      wordAt target.memory node=wordAt source.memory node:=by
    unfold wordAt
    rw [agree node (.header node member active)]
  refine ⟨nextPaths,pending,?_,?_,paths.pendingPending⟩
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

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.of_agreement
