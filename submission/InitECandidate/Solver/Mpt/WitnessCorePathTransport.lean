import InitECandidate.Solver.Mpt.WitnessCorePathRelabel

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Transport physical path separation across a real frame while keeping
only the remaining pending buffers. The target spans and completed model
must be derived from that frame; storage identity ignores only counters. -/
theorem ActiveRegistry.PathModel.transport (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg nextCfg : Configuration)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry target frontier db nextCfg)
    (paths : registry.PathModel) (nextPaths : next.nodes.PathModel) (validEq : next.nodes.graph.valid=registry.nodes.graph.valid)
    (mapping : ∀ current∈nextCfg.stack,∃ previous∈cfg.stack,current.data.payload.storage=previous.data.payload.storage)
    (agree : ∀ query,registry.nodes.graph.Footprint query → target.memory query=source.memory query)
    (pending : ∀ current∈nextCfg.stack,current.data.payload.PathBytes target) : next.PathModel := by
  have tags (node : BitVec 64) (member : registry.nodes.graph.valid node) (active : node≠0#64) :
      wordAt target.memory node=wordAt source.memory node:=by
    unfold wordAt
    rw [agree node (.header node member active)]
  refine ⟨nextPaths,pending,?_,?_,?_⟩
  · intro node member active tag index inside current inStack owner slot occupied payload offset offsetInside
    have oldMember : registry.nodes.graph.valid node:=by rwa [validEq] at member
    have oldTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64:=by rwa [tags node oldMember active] at tag
    have fields:=registry.nodes.graph.path_word_agreement target.memory agree node oldMember active oldTag
    rw [fields.2] at inside
    rw [fields.1]
    obtain ⟨previous,previousIn,same⟩:=mapping current inStack
    obtain ⟨oldSlot,oldOccupied,oldPayload⟩:=WitnessRecord.Payload.storage_branch current.data.payload previous.data.payload owner slot occupied payload same
    exact paths.nodePending node oldMember active oldTag index inside previous previousIn owner oldSlot oldOccupied oldPayload offset offsetInside
  · intro current inStack pointer length payload index inside owner member active offset offsetInside
    have oldMember : registry.nodes.graph.valid owner:=by rwa [validEq] at member
    rw [tags owner oldMember active] at offsetInside
    obtain ⟨previous,previousIn,same⟩:=mapping current inStack
    have oldPayload:=WitnessRecord.Payload.storage_extension current.data.payload previous.data.payload pointer length payload same
    exact paths.pendingNode previous previousIn pointer length oldPayload index inside owner oldMember active offset offsetInside
  · intro current inStack pointer length payload index inside other otherIn owner slot occupied ownerPayload offset offsetInside
    obtain ⟨previous,previousIn,same⟩:=mapping current inStack
    have oldPayload:=WitnessRecord.Payload.storage_extension current.data.payload previous.data.payload pointer length payload same
    obtain ⟨oldOther,oldOtherIn,otherSame⟩:=mapping other otherIn
    obtain ⟨oldSlot,oldOccupied,oldOwnerPayload⟩:=WitnessRecord.Payload.storage_branch other.data.payload oldOther.data.payload owner slot occupied ownerPayload otherSame
    exact paths.pendingPending previous previousIn pointer length oldPayload index inside oldOther oldOtherIn owner oldSlot oldOccupied oldOwnerPayload offset offsetInside

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.transport
