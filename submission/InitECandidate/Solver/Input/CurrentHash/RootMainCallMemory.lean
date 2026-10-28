import InitECandidate.Solver.Input.CurrentHash.RootMemory
import InitECandidate.Solver.Input.CurrentHash.RootMainCallCost

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Main's genuine root-hash call protects earlier metadata and restores the
entering heap. The complete decoder/workspace entry comes from its same
original decoder and root allocation, not a separate supplied hash contract. -/
theorem main_call_frame {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : WorkspaceEntry.Workspace current) (cursor query : BitVec 64)
    (heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) (before : query.toNat<cursor.toNat)
    (chunkAway : CopyGeneral.Away WorkspaceEntry.chunkPointer query 32) (outAway : CopyGeneral.Away root query 32)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)=(none,post)) :
    post.memory query=current.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,si,out⟩ := Invocation.environment current.code workspace.code origin.word root
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data current post (ofString "htr_new_payload_request") RootEntry.arguments actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans ready.args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have data := Invocation.at_callee ready workspace callee si out
  have frame := body_frame data cursor heap query before chunkAway outAway returned bodyRun
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.main_call_frame
