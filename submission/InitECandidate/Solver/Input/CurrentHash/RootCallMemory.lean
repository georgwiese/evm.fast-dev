import InitECandidate.Solver.Input.CurrentHash.RootCallCost

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The same real child call retains arbitrary earlier metadata and restores
the current root frontier. Its actual output slot and length workspace are
excluded; no future helper return or additional allocation room is supplied. -/
theorem State.call_frame {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}
    (state : State input source blob si record rq root array ch cursor length start size) (step : Step) (query : BitVec 64)
    (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away WorkspaceEntry.chunkPointer query 32)
    (actual : evaluateHOLFiniteState source step.call=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have args := state.arguments_read step
  have below : query.toNat<cursor.toNat := by have h:=state.heapAfter; omega
  cases step with
  | payload=>
    have frontier:=state.payload_frontier
    exact PayloadHash.call_frame source post blob record array cursor WorkspaceEntry.chunkPointer ch WorkspaceEntry.zeroPointer query length start size
      state.payload_context state.data.payload state.input_bounds.1 state.input_bounds.2.1 state.data.payloadArena state.data.payloadAligned frontier.1 frontier.2.1
      state.data.workspace.chunk state.data.workspace.chunkArena state.data.workspace.chunkAligned frontier.2.2 below chunkAway
      (by simpa only [Nat.mul_zero,BitVec.add_zero] using state.output_away 0 (by decide) query before) Step.payload.arguments args actual
  | headers=>
    exact PListMemory.call_frame source post (headerPointer input blob) cursor (BitVec.ofNat 64 (headerCount input)) WorkspaceEntry.chunkPointer (ch+32#64) WorkspaceEntry.zeroPointer query
      (headerCount input) (state.context query before) state.header_count_bound state.header_roots_arena (state.output_arena 1 (by decide)) (state.output_away 1 (by decide) query before)
      state.data.workspace.chunk state.data.workspace.chunkArena state.data.workspace.chunkAligned chunkAway Step.headers.arguments args actual
  | header=>
    have memory := MemoryAt.copy_normal source post Step.header.arguments (blob+18#64+8#64) (ch+64#64) query 32 args state.data.workspace.code state.data.workspace.domain
      state.header_copy_arena (state.output_arena 2 (by decide)) (state.output_away 2 (by decide) query before) actual
    have global := MemoryGlobals.call .copy (ofString "heap_ptr") source.code state.data.workspace.code (some none) Step.header.arguments source rfl
    change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source Step.header.call).2=_ at global
    rw [actual] at global
    exact ⟨memory,(congrArg Prod.snd global).trans state.heap⟩
  | requests=>
    obtain ⟨requestStart,requestSize,counts,requests⟩ := state.data.requestImage
    have frontier:=state.requests_frontier
    exact RequestsHash.call_frame source post blob rq cursor WorkspaceEntry.chunkPointer (ch+96#64) WorkspaceEntry.zeroPointer query requestStart requestSize counts
      state.requests_context requests frontier.1 state.data.workspace.chunk state.data.workspace.chunkArena state.data.workspace.chunkAligned frontier.2 below chunkAway
      (state.output_away 3 (by decide) query before) Step.requests.arguments args actual

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.call_frame
