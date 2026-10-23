import InitECandidate.Solver.Mpt.WitnessCorePathInvariant

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact

/-- Buffer identity ignores only the branch's changing loop counters. -/
def Payload.storage : Payload → Sum (BitVec 64×BitVec 64) (BitVec 64)
  | .extension pointer length=>.inl (pointer,length)
  | .branch node ..=>.inr node

theorem Payload.storage_extension (first second : Payload) (pointer length : BitVec 64)
    (extension : first=.extension pointer length) (same : first.storage=second.storage) : second=.extension pointer length := by
  cases second with
  | extension pointer' length'=>
    simp only [extension,Payload.storage,Sum.inl.injEq,Prod.mk.injEq] at same
    obtain ⟨rfl,rfl⟩:=same
    rfl
  | branch node slot occupied=>simp [extension,Payload.storage] at same

theorem Payload.storage_branch (first second : Payload) (node : BitVec 64) (slot : Fin 16) (occupied : Fin 17)
    (branch : first=.branch node slot occupied) (same : first.storage=second.storage) :
    ∃ slot' occupied',second=.branch node slot' occupied' := by
  cases second with
  | extension pointer length=>simp [branch,Payload.storage] at same
  | branch node' slot' occupied'=>
    simp only [branch,Payload.storage,Sum.inr.injEq] at same
    subst node'
    exact ⟨slot',occupied',rfl⟩

theorem Payload.PathBytes.same_storage (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : Payload) (bytes : second.PathBytes source) (same : first.storage=second.storage) : first.PathBytes source := by
  cases shape : first with
  | branch node slot occupied=>trivial
  | extension pointer length=>
    have other:=Payload.storage_extension first second pointer length shape same
    simpa only [shape,other,Payload.PathBytes] using bytes

end InitECandidate.Solver.Mpt.WitnessRecord

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Updating HASH/counters or popping a completed record retains exactly
the remaining buffers. This rule changes no bytes or graph membership. -/
theorem ActiveRegistry.PathModel.relabel (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg nextCfg : Configuration)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry source frontier db nextCfg)
    (paths : registry.PathModel) (nextPaths : next.nodes.PathModel) (validEq : next.nodes.graph.valid=registry.nodes.graph.valid)
    (mapping : ∀ current∈nextCfg.stack,∃ previous∈cfg.stack,current.data.payload.storage=previous.data.payload.storage) : next.PathModel := by
  refine ⟨nextPaths,?_,?_,?_,?_⟩
  · intro current member
    obtain ⟨previous,oldMember,same⟩:=mapping current member
    exact WitnessRecord.Payload.PathBytes.same_storage source current.data.payload previous.data.payload (paths.pending previous oldMember) same
  · intro node member active tag index inside current inStack owner slot occupied payload offset offsetInside
    have oldMember : registry.nodes.graph.valid node:=by rwa [validEq] at member
    obtain ⟨previous,previousIn,same⟩:=mapping current inStack
    obtain ⟨oldSlot,oldOccupied,oldPayload⟩:=WitnessRecord.Payload.storage_branch current.data.payload previous.data.payload owner slot occupied payload same
    exact paths.nodePending node oldMember active tag index inside previous previousIn owner oldSlot oldOccupied oldPayload offset offsetInside
  · intro current inStack pointer length payload index inside owner member active offset offsetInside
    have oldMember : registry.nodes.graph.valid owner:=by rwa [validEq] at member
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

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Payload.storage_extension
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Payload.storage_branch
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Payload.PathBytes.same_storage
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.relabel
