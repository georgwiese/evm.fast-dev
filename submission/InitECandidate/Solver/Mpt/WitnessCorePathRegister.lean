import InitECandidate.Solver.Mpt.WitnessCorePathRelabel

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Register a real completed node while retaining the remaining pending
buffers. The new node may precede children allocated while it was pending;
the actual cross-buffer separations, rather than fresh-node order, suffice. -/
theorem ActiveRegistry.PathModel.registered (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db node : BitVec 64) (cfg nextCfg : Configuration)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry source frontier db nextCfg)
    (paths : registry.PathModel) (nextPaths : next.nodes.PathModel)
    (members : ∀ current,next.nodes.graph.valid current → registry.nodes.graph.valid current ∨ current=node)
    (mapping : ∀ current∈nextCfg.stack,∃ previous∈cfg.stack,current.data.payload.storage=previous.data.payload.storage)
    (newPathApart : node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,∀ entry∈cfg.stack,∀ owner slot occupied,
        entry.data.payload=.branch owner slot occupied → ∀ offset<176,
        panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)≠byteAddress owner offset)
    (newOwnerApart : node≠0#64 → ∀ entry∈cfg.stack,∀ pointer length,entry.data.payload=.extension pointer length →
      ∀ index<length.toNat,∀ offset<TrieWalk.nodeBytes (wordAt source.memory node),
        panByteAlignHOL (width:=64) (byteAddress pointer index)≠byteAddress node offset) : next.PathModel := by
  refine ⟨nextPaths,?_,?_,?_,?_⟩
  · intro current member
    obtain ⟨previous,oldMember,same⟩:=mapping current member
    exact WitnessRecord.Payload.PathBytes.same_storage source current.data.payload previous.data.payload (paths.pending previous oldMember) same
  · intro current member active tag index inside entry inStack owner slot occupied payload offset offsetInside
    obtain ⟨previous,previousIn,same⟩:=mapping entry inStack
    obtain ⟨oldSlot,oldOccupied,oldPayload⟩:=WitnessRecord.Payload.storage_branch entry.data.payload previous.data.payload owner slot occupied payload same
    rcases members current member with prior|fresh
    · exact paths.nodePending current prior active tag index inside previous previousIn owner oldSlot oldOccupied oldPayload offset offsetInside
    · subst current
      exact newPathApart active tag index inside previous previousIn owner oldSlot oldOccupied oldPayload offset offsetInside
  · intro entry inStack pointer length payload index inside owner member active offset offsetInside
    obtain ⟨previous,previousIn,same⟩:=mapping entry inStack
    have oldPayload:=WitnessRecord.Payload.storage_extension entry.data.payload previous.data.payload pointer length payload same
    rcases members owner member with prior|fresh
    · exact paths.pendingNode previous previousIn pointer length oldPayload index inside owner prior active offset offsetInside
    · subst owner
      exact newOwnerApart active previous previousIn pointer length oldPayload index inside offset offsetInside
  · intro entry inStack pointer length payload index inside other otherIn owner slot occupied ownerPayload offset offsetInside
    obtain ⟨previous,previousIn,same⟩:=mapping entry inStack
    have oldPayload:=WitnessRecord.Payload.storage_extension entry.data.payload previous.data.payload pointer length payload same
    obtain ⟨oldOther,oldOtherIn,otherSame⟩:=mapping other otherIn
    obtain ⟨oldSlot,oldOccupied,oldOwnerPayload⟩:=WitnessRecord.Payload.storage_branch other.data.payload oldOther.data.payload owner slot occupied ownerPayload otherSame
    exact paths.pendingPending previous previousIn pointer length oldPayload index inside oldOther oldOtherIn owner oldSlot oldOccupied oldOwnerPayload offset offsetInside

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.registered
