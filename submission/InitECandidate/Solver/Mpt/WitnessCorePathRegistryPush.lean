import InitECandidate.Solver.Mpt.WitnessCorePathRegistryExtend

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A genuine fresh decoder record adds either a new extension buffer or
a new pending branch. Its actual allocation follows all old paths and
nodes, so no newly mutable branch can overwrite a pending path buffer. -/
theorem ActiveRegistry.PathModel.record_added (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg nextCfg : Configuration) (entry : Entry)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry source frontier db nextCfg)
    (paths : registry.PathModel) (nextPaths : next.nodes.PathModel) (stackEq : nextCfg.stack=entry::cfg.stack)
    (validEq : next.nodes.graph.valid=registry.nodes.graph.valid)
    (records : ∀ current∈cfg.stack,WitnessRecord.View source current.record db current.data)
    (bounded : ∀ current∈cfg.stack,current.data.BeforeHeap cfg.heap.toNat)
    (newView : WitnessRecord.View source entry.record db entry.data)
    (newBytes : entry.data.payload.PathBytes source) (fresh : cfg.heap.toNat≤entry.data.payload.startAddress) : next.PathModel := by
  have branchBounds (other : Entry) (member : other∈cfg.stack) (owner : BitVec 64) (slot : Fin 16) (occupied : Fin 17)
      (payload : other.data.payload=.branch owner slot occupied) :
      AllocatedBytes.Arena owner 176 ∧ owner.toNat+176≤cfg.heap.toNat:=by
    have owned:=(records other member).owned
    have before:=(bounded other member).2
    simp only [payload,WitnessRecord.Payload.Owned,WitnessRecord.Payload.endAddress] at owned before
    exact ⟨owned.1,before⟩
  refine ⟨nextPaths,?_,?_,?_,?_⟩
  · intro current member
    rw [stackEq] at member
    rcases List.mem_cons.mp member with same|older
    · subst current; exact newBytes
    · exact paths.pending current older
  · intro node member active tag index inside current inStack owner slot occupied payload offset offsetInside
    have oldMember : registry.nodes.graph.valid node:=by rwa [validEq] at member
    rw [stackEq] at inStack
    rcases List.mem_cons.mp inStack with same|older
    · subst current
      have span:=paths.nodes.bytes.span node oldMember active tag
      have before:=(paths.nodes.regions node oldMember active tag).2
      have owned:=newView.owned
      have lower:=fresh
      simp only [payload,WitnessRecord.Payload.Owned,WitnessRecord.Payload.startAddress] at owned lower
      exact span.apart_before source.memory source.memaddrs source.be _ owner _ 176 owned.1 (before.trans lower) index inside offset offsetInside
    · exact paths.nodePending node oldMember active tag index inside current older owner slot occupied payload offset offsetInside
  · intro current inStack pointer length payload index inside owner member active offset offsetInside
    have oldMember : registry.nodes.graph.valid owner:=by rwa [validEq] at member
    rw [stackEq] at inStack
    rcases List.mem_cons.mp inStack with same|older
    · subst current
      have span:=newBytes
      have lower:=fresh
      simp only [payload,WitnessRecord.Payload.PathBytes,WitnessRecord.Payload.startAddress] at span lower
      obtain ⟨floor,arena,aligned,before⟩:=registry.nodes.regions owner oldMember active
      exact span.1.apart_after source.memory source.memaddrs source.be pointer owner length.toNat _ span.2 arena (before.trans lower) index inside offset offsetInside
    · exact paths.pendingNode current older pointer length payload index inside owner oldMember active offset offsetInside
  · intro current inStack pointer length payload index inside other otherIn owner slot occupied ownerPayload offset offsetInside
    rw [stackEq] at inStack otherIn
    rcases List.mem_cons.mp inStack with same|older
    · subst current
      rcases List.mem_cons.mp otherIn with same|otherOld
      · subst other
        rw [payload] at ownerPayload
        cases ownerPayload
      · have span:=newBytes
        have lower:=fresh
        simp only [payload,WitnessRecord.Payload.PathBytes,WitnessRecord.Payload.startAddress] at span lower
        obtain ⟨arena,before⟩:=branchBounds other otherOld owner slot occupied ownerPayload
        exact span.1.apart_after source.memory source.memaddrs source.be pointer owner length.toNat 176 span.2 arena (before.trans lower) index inside offset offsetInside
    · rcases List.mem_cons.mp otherIn with same|otherOld
      · subst other
        have span:=paths.pending current older
        have before:=(bounded current older).2
        simp only [payload,WitnessRecord.Payload.PathBytes,WitnessRecord.Payload.endAddress] at span before
        have owned:=newView.owned
        have lower:=fresh
        simp only [ownerPayload,WitnessRecord.Payload.Owned,WitnessRecord.Payload.startAddress] at owned lower
        exact span.1.apart_before source.memory source.memaddrs source.be pointer owner length.toNat 176 owned.1 (before.trans lower) index inside offset offsetInside
      · exact paths.pendingPending current older pointer length payload index inside other otherOld owner slot occupied ownerPayload offset offsetInside

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.record_added
