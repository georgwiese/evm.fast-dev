import InitECandidate.Solver.Input.RequestRootHashPhaseHeap

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every actual normal original request-root phase preserves the fixed
copied/decoded input region, including SI and all later request metadata. -/
theorem phase_frame (phase : Phase) (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Ready data origin source lower upper ch out mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : PayloadHash.FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (run : evaluateHOLFiniteState source phase.call=(none,post)) : HashInput.Frame origin post lower upper := by
  have args := arguments_read phase data origin source lower upper budget ch out mark stp accel chunk zeros image layout actual
  obtain ⟨number,aligned,scratch,roots,outputs⟩ := data.common_geometry budget ch geometry
  have cursorBefore : upper≤(cursor ch).toNat := by omega
  constructor
  intro query low high
  have protection := separation.at_word source stp accel chunk zeros query lower actual.workspace small low
  have below : query.toNat<(cursor ch).toNat := by omega
  have rootsAway := CopyGeneral.Away.after ch query 128 geometry.aligned (by have h:=geometry.arena.upper; omega) (by omega)
  have away (slot : Nat) (inside : slot<4) : CopyGeneral.Away (ch+BitVec.ofNat 64 (32*slot)) query 32 :=
    CopyGeneral.Away.subrange ch query 128 (32*slot) 32 rootsAway (by omega)
  have frame : post.memory query=source.memory query := by
    cases phase with
    | payload=>
      have kept := (PayloadHash.call_normal data.payload origin source post lower upper budget ch (cursor ch) stp accel chunk zeros image.payload layout.payload actual.workspace actual.input actual.heap
        (data.payload_geometry budget ch geometry) ⟨AllocatedBytes.Arena.weaken ch 256 32 roots (by decide),geometry.aligned,before⟩ separation small cursorBefore Phase.payload.arguments args run).2
      exact (kept.words query low high).trans (actual.input.words query low high).symm
    | blobs=>
      exact PListChunks.call_memory source post data.blobs (cursor ch) (ch+32#64) (BitVec.ofNat 64 data.blobCount) stp accel chunk zeros query data.blobCount
        (by have a:=layout.blobsBound; have b:=layout.payload.budgetBound; omega) protection actual.heap layout.blobsArena (data.blob_geometry budget ch geometry) aligned (outputs 1 (by decide)) below (away 1 (by decide))
        Phase.blobs.arguments args run
    | parent=>
      exact MemoryAt.copy_normal source post Phase.parent.arguments data.parent (ch+64#64) query 32 args actual.workspace.sha.installed actual.workspace.sha.domain layout.parentArena (outputs 2 (by decide)) (away 2 (by decide)) run
    | requests=>
      obtain ⟨mapped,requestSeparation⟩ := data.request_geometry lower upper budget ch stp accel chunk layout geometry separation before
      exact RequestsHash.call_memory source post data.requests (cursor ch) (ch+96#64) stp accel chunk zeros query data.requestPointer data.requestCount budget protection
        (data.current_requests origin source lower upper budget image layout actual.input) actual.heap mapped requestSeparation below (away 3 (by decide)) Phase.requests.arguments args run
    | root=>
      have inputArena : AllocatedBytes.Arena ch (32*(4#64).toNat) := AllocatedBytes.Arena.weaken ch 256 _ roots (by decide)
      have bufferArena : AllocatedBytes.Arena (cursor ch) (32*max 1 (2*(4#64).toNat)) := AllocatedBytes.Arena.weaken _ _ _ scratch (by change 256≤data.scratchBytes budget; unfold Description.scratchBytes; omega)
      have outAway := CopyGeneral.Away.after out query 32 outputGeometry.aligned (by have h:=outputGeometry.arena.upper; omega) (by have h:=outputGeometry.before; omega)
      exact Merkle.call_memory source post ch 4#64 4#64 (cursor ch) out stp accel chunk zeros query 2 (by decide) (by decide) (by decide) protection actual.heap inputArena bufferArena aligned outputGeometry.arena below outAway Phase.root.arguments args run
  exact frame.trans (actual.input.words query low high)

/-- A reached normal phase reestablishes the entire actual caller/input
relation before the next literal original phase. -/
theorem phase_normal (phase : Phase) (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Ready data origin source lower upper ch out mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : PayloadHash.FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (run : evaluateHOLFiniteState source phase.call=(none,post)) : Ready data origin post lower upper ch out mark stp accel chunk zeros :=
  actual.after_call data origin source post lower upper ch out mark stp accel chunk zeros phase run
    (phase_heap phase data origin source post lower upper budget ch out mark stp accel chunk zeros image layout actual geometry separation small before run)
    (fun key different=>phase_globals phase key source.code actual.workspace.sha.installed different)
    (phase_frame phase data origin source post lower upper budget ch out mark stp accel chunk zeros image layout actual geometry outputGeometry separation small before run)

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.phase_frame
#print axioms InitECandidate.Solver.Input.RequestRootHash.phase_normal
