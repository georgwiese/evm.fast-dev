import InitECandidate.Solver.Input.CurrentHash.RootMainCallMemory

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}

/-- Actual earlier decoder memory survives main's real normal root call. The
boundaries are the initialized workspace and the returned root allocation;
no hasher success or extra allocation room is supplied. -/
theorem main_earlier_memory
    (ready : RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : WorkspaceEntry.Workspace current)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)=(none,post))
    (query : BitVec 64) (lower : 2701134640≤query.toNat) (before : query.toNat<root.toNat) :
    post.memory query=decoded.memory query := by
  obtain ⟨cursor,heap,afterRoot,bounded,aligned⟩ := ready.heap
  have away : CopyGeneral.Away root query 32 :=
    CopyGeneral.Away.after root query 32 ready.aligned (by have h:=ready.room; omega) before
  have frame := main_call_frame ready workspace cursor query heap (by omega) (metadata_chunk_away query lower) away actual
  exact frame.1.trans (congrFun ready.memory query)

/-- The normal caller retains main's exact SI binding, initialized arenas and
workspace, and its entering persistent frontier. These facts belong to the
same actual call, including any changes to hash output and host observations. -/
theorem main_returned_state
    (ready : RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : WorkspaceEntry.Workspace current)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)=(none,post)) :
    CurrentStartup.ArenaState post ∧ WorkspaceEntry.Workspace post ∧
    NormalHeapEffects.AtLeast (root.toNat+32) post ∧
    post.locals.lookup (ofString "si")=some (.val (.word origin.word)) := by
  have next := workspace.after_call .htr_new_payload_request (some none) RootEntry.arguments none actual
  have kept (cursorKey : Cursor) := Effects.call_preserves cursorKey current.code workspace.code .htr_new_payload_request (some none) RootEntry.arguments current rfl
  have scratch := kept .scratch
  change GlobalEffects.erase (key .scratch) (evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)).2=_ at scratch
  rw [actual] at scratch
  have frame := kept .frame
  change GlobalEffects.erase (key .frame) (evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)).2=_ at frame
  rw [actual] at frame
  have arena : CurrentStartup.ArenaState post := ⟨(congrArg Prod.snd scratch).trans ready.arena.scratch,
    (congrArg Prod.snd frame).trans ready.arena.frame,next.domain,next.code⟩
  obtain ⟨cursor,heap,afterRoot,bounded,aligned⟩ := ready.heap
  have away : CopyGeneral.Away root 0#64 32 :=
    CopyGeneral.Away.after root 0#64 32 ready.aligned (by have h:=ready.room; omega)
      (by have h:=ready.rootAfter; change 0<root.toNat; omega)
  have heapFrame := main_call_frame ready workspace cursor 0#64 heap (by have h:=ready.rootAfter; change 0<cursor.toNat; omega)
    (CopyGeneral.Away.after WorkspaceEntry.chunkPointer 0#64 32 (by decide) (by decide) (by decide)) away actual
  exact ⟨arena,next,⟨cursor,heapFrame.2,afterRoot,bounded,aligned⟩,
    (CallNormal.ignored_lookup current post (ofString "si") (ofString "htr_new_payload_request") RootEntry.arguments actual).trans ready.si⟩

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.main_earlier_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.main_returned_state
