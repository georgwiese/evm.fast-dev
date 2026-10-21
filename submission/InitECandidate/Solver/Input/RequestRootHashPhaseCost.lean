import InitECandidate.Solver.Input.RequestRootHashGlobals

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every actual original phase is bounded at its current ABI, heap and
preserved decoded inputs. Failed non-timeout prefixes remain included. -/
theorem phase_cost (phase : Phase) (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Ready data origin source lower upper ch out mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outArena : AllocatedBytes.Arena out 32)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source phase.call=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤phase.price data := by
  have args := arguments_read phase data origin source lower upper budget ch out mark stp accel chunk zeros image layout actual
  obtain ⟨number,aligned,scratch,roots,outputs⟩ := data.common_geometry budget ch geometry
  have cursorBefore : upper≤(cursor ch).toNat := by omega
  cases phase with
  | payload=>
    exact PayloadHash.call_cost data.payload origin source post lower upper budget ch (cursor ch) stp accel chunk zeros image.payload layout.payload actual.workspace actual.input actual.heap
      (data.payload_geometry budget ch geometry) separation small cursorBefore (some none) Phase.payload.arguments args result run notTimeout
  | blobs=>
    exact PListChunks.call_cost source post data.blobs (cursor ch) (ch+32#64) (BitVec.ofNat 64 data.blobCount) stp accel chunk zeros data.blobCount
      (by have a:=layout.blobsBound; have b:=layout.payload.budgetBound; omega) actual.workspace actual.heap layout.blobsArena (data.blob_geometry budget ch geometry) aligned (outputs 1 (by decide))
      (some none) Phase.blobs.arguments args result run notTimeout
  | parent=>
    have priced := CopyGeneral.call_cost_arena source Phase.parent.arguments data.parent (ch+64#64) 32 args (CopyGeneral.original_code source.code actual.workspace.sha.installed) actual.workspace.sha.domain layout.parentArena (outputs 2 (by decide))
    change source.clock-(evaluateHOLFiniteState source Phase.parent.call).2.clock≤_ at priced
    rw [run] at priced
    exact priced.trans (Nat.add_le_add_right (CopyGeneral.cost_word_multiple data.parent (ch+64#64) 32 (by decide)) 1)
  | requests=>
    obtain ⟨mapped,requestSeparation⟩ := data.request_geometry lower upper budget ch stp accel chunk layout geometry separation before
    exact RequestsHash.call_cost source post data.requests (cursor ch) (ch+96#64) stp accel chunk zeros data.requestPointer data.requestCount budget actual.workspace
      (data.current_requests origin source lower upper budget image layout actual.input) actual.heap mapped requestSeparation (some none) Phase.requests.arguments args result run notTimeout
  | root=>
    have inputArena : AllocatedBytes.Arena ch (32*(4#64).toNat) := AllocatedBytes.Arena.weaken ch 256 _ roots (by decide)
    have bufferArena : AllocatedBytes.Arena (cursor ch) (32*max 1 (2*(4#64).toNat)) := AllocatedBytes.Arena.weaken _ _ _ scratch (by change 256≤data.scratchBytes budget; unfold Description.scratchBytes; omega)
    exact Merkle.call_cost source post ch 4#64 4#64 (cursor ch) out zeros stp accel 2 (by decide) (by decide) (by decide) actual.workspace.sha actual.heap actual.workspace.zerosLocal
      inputArena bufferArena aligned outArena actual.workspace.zeroArena (some none) Phase.root.arguments args result run notTimeout

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.phase_cost
