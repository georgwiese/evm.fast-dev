import InitECandidate.Solver.Input.CurrentHash.HtrNewPayloadRequest

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace Effects

theorem body_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (routine : Code.Routine) :
    GlobalEffects.Preserves (key cursor) code (Code.body routine) := by
  cases routine with
  | trap_with => exact CurrentStartup.TrapWith.preserves cursor code installed
  | alloc => exact CurrentStartup.Alloc.preserves cursor code installed
  | heap_mark => exact CurrentStartup.HeapMark.preserves cursor code installed
  | heap_release => exact CurrentStartup.HeapRelease.preserves cursor code installed
  | ceil_log2 => exact CeilLog2.preserves cursor code installed
  | max => exact Max.preserves cursor code installed
  | memcpy => exact CurrentStartup.Memcpy.preserves cursor code installed
  | memzero => exact CurrentStartup.Memzero.preserves cursor code installed
  | sha256_pair => exact Sha256Pair.preserves cursor code installed
  | merkleize => exact Merkleize.preserves cursor code installed
  | st_le32 => exact CurrentStartup.StLe32.preserves cursor code installed
  | st_le64 => exact CurrentStartup.StLe64.preserves cursor code installed
  | mix_in_length => exact MixInLength.preserves cursor code installed
  | pack_bytes => exact PackBytes.preserves cursor code installed
  | htr_bytes_list => exact HtrBytesList.preserves cursor code installed
  | htr_bytes_vector => exact HtrBytesVector.preserves cursor code installed
  | merkleize_progressive => exact MerkleizeProgressive.preserves cursor code installed
  | htr_plist_chunks => exact HtrPlistChunks.preserves cursor code installed
  | htr_pbytes => exact HtrPbytes.preserves cursor code installed
  | htr_pcontainer => exact HtrPcontainer.preserves cursor code installed
  | htr_u64_at => exact HtrU64At.preserves cursor code installed
  | htr_withdrawal => exact HtrWithdrawal.preserves cursor code installed
  | htr_payload => exact HtrPayload.preserves cursor code installed
  | htr_bdep => exact HtrBdep.preserves cursor code installed
  | htr_bexit => exact HtrBexit.preserves cursor code installed
  | htr_cons => exact HtrCons.preserves cursor code installed
  | htr_deposit => exact HtrDeposit.preserves cursor code installed
  | htr_wdreq => exact HtrWdreq.preserves cursor code installed
  | htr_request_list => exact HtrRequestList.preserves cursor code installed
  | htr_requests => exact HtrRequests.preserves cursor code installed
  | htr_new_payload_request => exact HtrNewPayloadRequest.preserves cursor code installed

theorem call_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (routine : Code.Routine)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves (key cursor) code (.call (GlobalEffects.callInfo destination) (Code.name routine) arguments) :=
  GlobalEffects.call_body (key cursor) code destination (Code.name routine) arguments
    (Code.formals routine) (Code.body routine) (Code.shape routine)
    (Code.installed code installed routine) (body_preserves cursor code installed routine)

end Effects
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.Effects.body_preserves
#print axioms InitECandidate.Solver.Input.CurrentHash.Effects.call_preserves
