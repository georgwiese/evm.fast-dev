import InitECandidate.Solver.Input.CurrentHash.BytesListMemory
import InitECandidate.Solver.Input.CurrentHash.BytesVectorMemory
import InitECandidate.Solver.Input.CurrentHash.BytesCallCost

namespace InitECandidate.Solver.Input.CurrentHash.BytesCallMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open BytesCallCost

/-- The actual three/four-word byte-hash callers inherit both memory and heap
frames from the same checked callee return. No temporary-allocation room or
successful future helper is assumed at caller entry. -/
theorem frame (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor limit out zeros chunk query : BitVec 64) (n budget : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (lengthSmall : n+64<2^64) (small : budget<58)
    (chunksBound : PackBytes.chunks n≤2^budget) (limitBound : kind=.list → limit.toNat≤2^budget)
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32)
    (outAligned : kind=.vector → out.toNat%8=0) (outAway : CopyGeneral.Away out query 32)
    (chunkData : kind=.list → source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)) ∧
      AllocatedBytes.Arena chunk 32 ∧ chunk.toNat%8=0 ∧ CopyGeneral.Away chunk query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values kind p limit out n))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name (routine kind)) arguments)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,pointer,length,output,maximum⟩ := environment kind source.code context.installed p limit out n
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (Code.name (routine kind)) arguments actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have image : target.memory query=source.memory query ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
    cases kind with
    | vector =>
      exact BytesVectorMemory.body_frame (callEntryStateHOLFinite source callee) target p cursor out zeros query n budget
        (context.at_callee callee) ⟨pointer,length,output⟩ lengthSmall small chunksBound inputArena outArena (outAligned rfl) outAway returned bodyRun
    | list =>
      obtain ⟨chunkCell,chunkArena,chunkAligned,chunkAway⟩ := chunkData rfl
      exact BytesListMemory.body_frame (callEntryStateHOLFinite source callee) target p cursor limit out zeros chunk query n budget
        (context.at_callee callee) ⟨pointer,length,maximum rfl,output⟩ lengthSmall small chunksBound (limitBound rfl)
        inputArena outArena outAway chunkCell chunkArena chunkAligned chunkAway returned bodyRun
  rw [endpoint]
  exact image

end InitECandidate.Solver.Input.CurrentHash.BytesCallMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.BytesCallMemory.frame
