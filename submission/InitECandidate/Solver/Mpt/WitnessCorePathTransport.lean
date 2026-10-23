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

/-- Transport real old paths through a physical mutation and register
one completed node while retaining only the actual remaining buffers. -/
theorem ActiveRegistry.PathModel.transport_registered (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db node : BitVec 64) (cfg nextCfg : Configuration)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry target frontier db nextCfg)
    (paths : registry.PathModel) (nextPaths : next.nodes.PathModel)
    (members : ∀ current,next.nodes.graph.valid current → registry.nodes.graph.valid current ∨ current=node)
    (mapping : ∀ current∈nextCfg.stack,∃ previous∈cfg.stack,current.data.payload.storage=previous.data.payload.storage)
    (agree : ∀ query,registry.nodes.graph.Footprint query → target.memory query=source.memory query)
    (pending : ∀ current∈nextCfg.stack,current.data.payload.PathBytes target)
    (newPathApart : node≠0#64 → (wordAt target.memory node=1#64 ∨ wordAt target.memory node=2#64) →
      ∀ index<(wordAt target.memory (node+40#64)).toNat,∀ entry∈cfg.stack,∀ owner slot occupied,
        entry.data.payload=.branch owner slot occupied → ∀ offset<176,
        panByteAlignHOL (width:=64) (byteAddress (wordAt target.memory (node+32#64)) index)≠byteAddress owner offset)
    (newOwnerApart : node≠0#64 → ∀ entry∈cfg.stack,∀ pointer length,entry.data.payload=.extension pointer length →
      ∀ index<length.toNat,∀ offset<TrieWalk.nodeBytes (wordAt target.memory node),
        panByteAlignHOL (width:=64) (byteAddress pointer index)≠byteAddress node offset) : next.PathModel := by
  have tags (current : BitVec 64) (member : registry.nodes.graph.valid current) (active : current≠0#64) : wordAt target.memory current=wordAt source.memory current:=by
    unfold wordAt
    rw [agree current (.header current member active)]
  refine ⟨nextPaths,pending,?_,?_,?_⟩
  · intro current member active tag index inside entry inStack owner slot occupied payload offset offsetInside
    obtain ⟨previous,previousIn,same⟩:=mapping entry inStack
    obtain ⟨oldSlot,oldOccupied,oldPayload⟩:=WitnessRecord.Payload.storage_branch entry.data.payload previous.data.payload owner slot occupied payload same
    rcases members current member with prior|fresh
    · have oldTag : wordAt source.memory current=1#64 ∨ wordAt source.memory current=2#64:=by rwa [tags current prior active] at tag
      have fields:=registry.nodes.graph.path_word_agreement target.memory agree current prior active oldTag
      rw [fields.2] at inside
      rw [fields.1]
      exact paths.nodePending current prior active oldTag index inside previous previousIn owner oldSlot oldOccupied oldPayload offset offsetInside
    · subst current
      exact newPathApart active tag index inside previous previousIn owner oldSlot oldOccupied oldPayload offset offsetInside
  · intro entry inStack pointer length payload index inside owner member active offset offsetInside
    obtain ⟨previous,previousIn,same⟩:=mapping entry inStack
    have oldPayload:=WitnessRecord.Payload.storage_extension entry.data.payload previous.data.payload pointer length payload same
    rcases members owner member with prior|fresh
    · rw [tags owner prior active] at offsetInside
      exact paths.pendingNode previous previousIn pointer length oldPayload index inside owner prior active offset offsetInside
    · subst owner
      exact newOwnerApart active previous previousIn pointer length oldPayload index inside offset offsetInside
  · intro entry inStack pointer length payload index inside other otherIn owner slot occupied ownerPayload offset offsetInside
    obtain ⟨previous,previousIn,same⟩:=mapping entry inStack
    have oldPayload:=WitnessRecord.Payload.storage_extension entry.data.payload previous.data.payload pointer length payload same
    obtain ⟨oldOther,oldOtherIn,otherSame⟩:=mapping other otherIn
    obtain ⟨oldSlot,oldOccupied,oldOwnerPayload⟩:=WitnessRecord.Payload.storage_branch other.data.payload oldOther.data.payload owner slot occupied ownerPayload otherSame
    exact paths.pendingPending previous previousIn pointer length oldPayload index inside oldOther oldOtherIn owner oldSlot oldOccupied oldOwnerPayload offset offsetInside

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.transport

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.transport_registered
