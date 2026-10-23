import InitECandidate.Solver.Mpt.WitnessCoreRegistryPayloadFrame
import InitECandidate.Solver.Mpt.WitnessCorePathRelabel
import InitECandidate.Solver.Mpt.WitnessRecordPayloadUnique

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Registry facts depend on actual payload fields, heap and phase.
Ghost row descriptions, cursor descriptions and running flags may differ
when the same physical payloads have been established independently. -/
theorem ActiveRegistry.of_payload_paths (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (first second : Configuration) (registry : ActiveRegistry source frontier db first) (paths : registry.PathModel)
    (heapEq : second.heap=first.heap) (phaseEq : second.phase=first.phase)
    (payloads : ∀ current∈second.stack,∃ prior∈first.stack,current.data.payload=prior.data.payload) :
    ∃ next : ActiveRegistry source frontier db second,next.PathModel := by
  obtain ⟨heap,cursor,stack,phase,running⟩:=first
  obtain ⟨nextHeap,nextCursor,nextStack,nextPhase,nextRunning⟩:=second
  change nextHeap=heap at heapEq
  subst nextHeap
  change nextPhase=phase at phaseEq
  subst nextPhase
  have children : ChildViews source registry.nodes.graph.valid nextStack:=by
    intro current member
    obtain ⟨prior,priorMember,same⟩:=payloads current member
    have old:=registry.children prior priorMember
    unfold ChildView at old ⊢
    rw [same]
    exact old
  have excluded : ∀ current∈nextStack,∀ node index occupied,current.data.payload=.branch node index occupied → registry.nodes.graph.Excludes node 176:=by
    intro current member node index occupied currentPayload
    obtain ⟨prior,priorMember,same⟩:=payloads current member
    exact registry.excludes prior priorMember node index occupied (same.symm.trans currentPayload)
  let next : ActiveRegistry source frontier db ⟨heap,nextCursor,nextStack,phase,nextRunning⟩:=⟨registry.nodes,children,excluded,registry.returned⟩
  have nextPaths : next.PathModel:=paths.relabel source frontier db _ _ registry next paths.nodes rfl (by
    intro current member
    obtain ⟨prior,priorMember,same⟩:=payloads current member
    exact ⟨prior,priorMember,congrArg WitnessRecord.Payload.storage same⟩)
  exact ⟨next,nextPaths⟩

/-- Two real views of the same continuing record identify the same
physical branch payload/counters, allowing their ghost descriptions to
be joined without assuming unique RLP item descriptions. -/
theorem ActiveRegistry.replace_head_paths (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap cursor : BitVec 64) (entry nextEntry : Entry) (rest : List Entry)
    (phase : WitnessStackRank.Phase) (running : Bool)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,phase,running⟩) (paths : registry.PathModel)
    (sameRecord : nextEntry.record=entry.record)
    (first : WitnessRecord.View source entry.record db entry.data)
    (second : WitnessRecord.View source nextEntry.record db nextEntry.data) :
    ∃ next : ActiveRegistry source frontier db ⟨heap,cursor,nextEntry::rest,phase,running⟩,next.PathModel := by
  rw [sameRecord] at second
  have same:=first.payload_unique source entry.record db entry.data nextEntry.data second
  apply ActiveRegistry.of_payload_paths source frontier db ⟨heap,cursor,entry::rest,phase,running⟩ ⟨heap,cursor,nextEntry::rest,phase,running⟩ registry paths rfl rfl
  intro current member
  rcases List.mem_cons.mp member with new|older
  · subst current; exact ⟨entry,List.mem_cons_self,same.symm⟩
  · exact ⟨current,List.mem_cons_of_mem entry older,rfl⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.of_payload_paths
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.replace_head_paths
