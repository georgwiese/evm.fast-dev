import InitECandidate.Solver.Mpt.WitnessCoreRegistryFrame
import InitECandidate.Solver.Mpt.WitnessRecordPayloadUnique

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Registry facts depend on actual payload fields, heap and phase.
Ghost row descriptions, cursor descriptions and running flags may differ
when the same physical payloads have been established independently. -/
theorem ActiveRegistry.of_payloads (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (first second : Configuration) (registry : ActiveRegistry source frontier db first)
    (heapEq : second.heap=first.heap) (phaseEq : second.phase=first.phase)
    (payloads : ∀ current∈second.stack,∃ prior∈first.stack,current.data.payload=prior.data.payload) :
    Nonempty (ActiveRegistry source frontier db second) := by
  obtain ⟨heap,cursor,stack,phase,running⟩:=first
  obtain ⟨nextHeap,nextCursor,nextStack,nextPhase,nextRunning⟩:=second
  change nextHeap=heap at heapEq
  subst nextHeap
  change nextPhase=phase at phaseEq
  subst nextPhase
  refine ⟨⟨registry.nodes,?_,?_,registry.returned⟩⟩
  · intro current member
    obtain ⟨prior,priorMember,same⟩:=payloads current member
    have old:=registry.children prior priorMember
    unfold ChildView at old ⊢
    rw [same]
    exact old
  · intro current member node index occupied currentPayload
    obtain ⟨prior,priorMember,same⟩:=payloads current member
    exact registry.excludes prior priorMember node index occupied (same.symm.trans currentPayload)

/-- Two real views of the same continuing record identify the same
physical branch payload/counters, allowing their ghost descriptions to
be joined without assuming unique RLP item descriptions. -/
theorem ActiveRegistry.replace_head (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap cursor : BitVec 64) (entry nextEntry : Entry) (rest : List Entry)
    (phase : WitnessStackRank.Phase) (running : Bool)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,phase,running⟩)
    (sameRecord : nextEntry.record=entry.record)
    (first : WitnessRecord.View source entry.record db entry.data)
    (second : WitnessRecord.View source nextEntry.record db nextEntry.data) :
    Nonempty (ActiveRegistry source frontier db ⟨heap,cursor,nextEntry::rest,phase,running⟩) := by
  rw [sameRecord] at second
  have same:=first.payload_unique source entry.record db entry.data nextEntry.data second
  apply ActiveRegistry.of_payloads source frontier db ⟨heap,cursor,entry::rest,phase,running⟩ ⟨heap,cursor,nextEntry::rest,phase,running⟩ registry rfl rfl
  intro current member
  rcases List.mem_cons.mp member with new|older
  · subst current; exact ⟨entry,List.mem_cons_self,same.symm⟩
  · exact ⟨current,List.mem_cons_of_mem entry older,rfl⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.of_payloads
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.replace_head
