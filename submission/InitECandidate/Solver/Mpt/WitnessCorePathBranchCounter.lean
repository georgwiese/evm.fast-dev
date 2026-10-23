import InitECandidate.Solver.Mpt.WitnessCorePathAgreement
import InitECandidate.Solver.Mpt.WitnessCoreRegistryBranchPrefix

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The real pending branch child/OCC stores preserve every path byte.
The persistent child slot is separated from paths by the current model;
the actual OCC word is below all path backing words in scratch. -/
theorem ActiveRegistry.PathModel.branch_counter (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db node child : BitVec 64) (cfg : Configuration) (entry : Entry) (index : Fin 16) (occupied : Fin 17)
    (registry : ActiveRegistry source frontier db cfg)
    (next : ActiveRegistry (branchCounterEntry source entry.record node child index occupied) frontier db cfg)
    (paths : registry.PathModel) (validEq : next.nodes.graph.valid=registry.nodes.graph.valid)
    (view : View source db cfg.cursor.toNat cfg.heap.toNat cfg.stack) (inStack : entry∈cfg.stack)
    (payload : entry.data.payload=.branch node index occupied) (frontierLower : 2713731432≤frontier) : next.PathModel := by
  let post:=branchCounterEntry source entry.record node child index occupied
  have head:=view.records entry inStack
  have arena:=head.owned
  simp only [payload,WitnessRecord.Payload.Owned] at arena
  have domain : post.memaddrs=source.memaddrs:=by unfold post branchCounterEntry occupancyState; split <;> rfl
  have endian : post.be=source.be:=by unfold post branchCounterEntry occupancyState; split <;> rfl
  have agree : ∀ query,registry.nodes.graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.nodes.graph.footprint_bounds frontier cfg.heap.toNat registry.nodes.regions query required
    have outside:=registry.nodes.graph.excluded_footprint frontier cfg.heap.toNat registry.nodes.regions node 176
      (registry.excludes entry inStack node index occupied payload) query required
    exact branch_counter_outside_memory source entry.record node child index occupied arena.1 head.ceiling query (frontierLower.trans bounds.1) outside
  have pathMemory (pointer : BitVec 64) (length : Nat) (span : TrieWalk.NibbleSpan source.memory source.memaddrs source.be pointer length)
      (floor : 2713731432≤pointer.toNat)
      (apart : ∀ byteIndex<length,panByteAlignHOL (width:=64) (byteAddress pointer byteIndex)≠WitnessRecord.childAddress node index) :
      ∀ byteIndex<length,post.memory (panByteAlignHOL (width:=64) (byteAddress pointer byteIndex))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress pointer byteIndex)):=by
    intro byteIndex inside
    have number:=byteAddress_toNat pointer byteIndex (by have fits:=span.fits; omega)
    have recordNumber : (entry.record+40#64).toNat=entry.record.toNat+40:=
      byteAddress_toNat entry.record 40 (by have ceiling:=head.ceiling; omega)
    apply branch_counter_entry_memory source entry.record node child index occupied _ (apart byteIndex inside)
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [AllocatedBytes.aligned_number,number,recordNumber] at equal
    have ceiling:=head.ceiling
    omega
  have bytes : ∀ current,registry.nodes.graph.valid current → current≠0#64 → (wordAt source.memory current=1#64 ∨ wordAt source.memory current=2#64) →
      ∀ byteIndex<(wordAt source.memory (current+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (current+32#64)) byteIndex))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (current+32#64)) byteIndex)):=by
    intro current member active tag
    exact pathMemory _ _ (paths.nodes.bytes.span current member active tag) (frontierLower.trans (paths.nodes.regions current member active tag).1)
      (fun byteIndex inside=>paths.nodePending current member active tag byteIndex inside entry inStack node index occupied payload (32+8*index.val)
        (by have bound:=index.isLt; omega))
  have nodes : next.nodes.PathModel:=
    ⟨paths.nodes.bytes.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be registry.nodes.graph next.nodes.graph validEq domain endian agree bytes,
      paths.nodes.regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.nodes.graph next.nodes.graph frontier cfg.heap.toNat validEq agree,
      paths.nodes.separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.nodes.graph next.nodes.graph validEq agree⟩
  have pending : ∀ current∈cfg.stack,current.data.payload.PathBytes post:=by
    intro current member
    cases currentPayload : current.data.payload with
    | branch owner slot used=>trivial
    | extension pointer length=>
      have span:=paths.pending current member
      simp only [currentPayload,WitnessRecord.Payload.PathBytes] at span
      have floor:=(view.records current member).payloadFloor
      simp only [currentPayload,WitnessRecord.Payload.startAddress] at floor
      change TrieWalk.NibbleSpan post.memory post.memaddrs post.be pointer length.toNat ∧ pointer.toNat%8=0
      exact ⟨span.1.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be pointer length.toNat domain endian
        (pathMemory pointer length.toNat span.1 floor (fun byteIndex inside=>paths.pendingPending current member pointer length currentPayload byteIndex inside
          entry inStack node index occupied payload (32+8*index.val) (by have bound:=index.isLt; omega))),span.2⟩
  exact paths.of_agreement source post frontier db cfg registry next nodes validEq agree pending

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.branch_counter
