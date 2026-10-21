import InitECandidate.Solver.Input.RequestRootHashPhaseCost

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem phase_heap (phase : Phase) (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Ready data origin source lower upper ch out mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (run : evaluateHOLFiniteState source phase.call=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor ch))) := by
  have args := arguments_read phase data origin source lower upper budget ch out mark stp accel chunk zeros image layout actual
  obtain ⟨number,aligned,scratch,roots,outputs⟩ := data.common_geometry budget ch geometry
  have cursorBefore : upper≤(cursor ch).toNat := by omega
  cases phase with
  | payload=>
    exact (PayloadHash.call_normal data.payload origin source post lower upper budget ch (cursor ch) stp accel chunk zeros image.payload layout.payload actual.workspace actual.input actual.heap
      (data.payload_geometry budget ch geometry) ⟨AllocatedBytes.Arena.weaken ch 256 32 roots (by decide),geometry.aligned,before⟩ separation small cursorBefore Phase.payload.arguments args run).1
  | blobs=>
    exact PListChunks.ignored_return_heap source post data.blobs (cursor ch) (ch+32#64) (BitVec.ofNat 64 data.blobCount) stp accel chunk zeros data.blobCount
      (by have a:=layout.blobsBound; have b:=layout.payload.budgetBound; omega) actual.workspace actual.heap layout.blobsArena (data.blob_geometry budget ch geometry) aligned (outputs 1 (by decide))
      Phase.blobs.arguments args run
  | parent=>
    have frame := GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "memcpy") Phase.parent.arguments CopyGeneral.formals Copy32.body .one
      (CopyGeneral.original_code source.code actual.workspace.sha.installed) (Copy32.globals (ofString "heap_ptr") source.code) source rfl
    change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source Phase.parent.call).2=_ at frame
    rw [run] at frame
    exact (congrArg Prod.snd frame).trans actual.heap
  | requests=>
    obtain ⟨mapped,requestSeparation⟩ := data.request_geometry lower upper budget ch stp accel chunk layout geometry separation before
    exact RequestsHash.ignored_return_heap source post data.requests (cursor ch) (ch+96#64) stp accel chunk zeros data.requestPointer data.requestCount budget actual.workspace
      (data.current_requests origin source lower upper budget image layout actual.input) actual.heap mapped requestSeparation Phase.requests.arguments args run
  | root=>
    have inputArena : AllocatedBytes.Arena ch (32*(4#64).toNat) := AllocatedBytes.Arena.weaken ch 256 _ roots (by decide)
    have bufferArena : AllocatedBytes.Arena (cursor ch) (32*max 1 (2*(4#64).toNat)) := AllocatedBytes.Arena.weaken _ _ _ scratch (by change 256≤data.scratchBytes budget; unfold Description.scratchBytes; omega)
    exact Merkle.ignored_return_heap source post ch 4#64 4#64 (cursor ch) out stp accel 2 (by decide) (by decide) (by decide) actual.workspace.sha actual.heap
      inputArena bufferArena aligned Phase.root.arguments args run

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.phase_heap
