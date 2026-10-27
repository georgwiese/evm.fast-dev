import InitECandidate.Solver.Input.CurrentStartup.Sha256Init
import InitECandidate.Solver.Input.CurrentStartup.KeccakInit
import InitECandidate.Solver.Input.CurrentStartup.SszInit
import InitECandidate.Solver.Input.CurrentStartup.MptInit
import InitECandidate.Solver.Input.CurrentStartup.U256WsInit
import InitECandidate.Solver.Input.CurrentStartup.Secp256k1Init
import InitECandidate.Solver.Input.CurrentStartup.Bn254Init
import InitECandidate.Solver.Input.CurrentStartup.BlsPrecompilesInit
import InitECandidate.Solver.Input.CurrentStartup.Ripemd160Init
import InitECandidate.Solver.Input.CurrentStartup.Blake2Init
import InitECandidate.Solver.Input.CurrentStartup.HeaderInit
import InitECandidate.Solver.Input.CurrentStartup.EvmInit
import InitECandidate.Solver.Input.CurrentStartup.ForkInit
import InitECandidate.Solver.Input.CurrentStartup.DecodeHostInput
import InitECandidate.Solver.Input.CurrentStartup.SerializeResult
import InitECandidate.Solver.Input.CurrentStartup.OutputWrite

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace Effects

theorem body_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (routine : Code.Routine) :
    GlobalEffects.Preserves (key cursor) code (Code.body routine) := by
  cases routine with
  | trap_with => exact TrapWith.preserves cursor code installed
  | alloc => exact Alloc.preserves cursor code installed
  | sha256_init => exact Sha256Init.preserves cursor code installed
  | keccak_init => exact KeccakInit.preserves cursor code installed
  | ssz_init => exact SszInit.preserves cursor code installed
  | keccak_f1600 => exact KeccakF1600.preserves cursor code installed
  | keccak_absorb_block => exact KeccakAbsorbBlock.preserves cursor code installed
  | memcpy => exact Memcpy.preserves cursor code installed
  | memzero => exact Memzero.preserves cursor code installed
  | keccak256 => exact Keccak256.preserves cursor code installed
  | mpt_init => exact MptInit.preserves cursor code installed
  | u256_ws_init => exact U256WsInit.preserves cursor code installed
  | secp256k1_init => exact Secp256k1Init.preserves cursor code installed
  | bn254_init => exact Bn254Init.preserves cursor code installed
  | bls_consts_init => exact BlsConstsInit.preserves cursor code installed
  | bls_lib_init => exact BlsLibInit.preserves cursor code installed
  | bls_precompiles_init => exact BlsPrecompilesInit.preserves cursor code installed
  | ripemd160_init => exact Ripemd160Init.preserves cursor code installed
  | blake2_init => exact Blake2Init.preserves cursor code installed
  | header_init => exact HeaderInit.preserves cursor code installed
  | heap_mark => exact HeapMark.preserves cursor code installed
  | heap_release => exact HeapRelease.preserves cursor code installed
  | evm_init => exact EvmInit.preserves cursor code installed
  | st_be32 => exact StBe32.preserves cursor code installed
  | bswap64 => exact Bswap64.preserves cursor code installed
  | st_be64 => exact StBe64.preserves cursor code installed
  | addr_from_words => exact AddrFromWords.preserves cursor code installed
  | fork_init => exact ForkInit.preserves cursor code installed
  | ssz_fail => exact SszFail.preserves cursor code installed
  | ssz_split_var_list => exact SszSplitVarList.preserves cursor code installed
  | decode_bytes_list => exact DecodeBytesList.preserves cursor code installed
  | ssz_check_offsets => exact SszCheckOffsets.preserves cursor code installed
  | udivmod => exact Udivmod.preserves cursor code installed
  | ssz_fixed_list_count => exact SszFixedListCount.preserves cursor code installed
  | decode_payload => exact DecodePayload.preserves cursor code installed
  | decode_requests => exact DecodeRequests.preserves cursor code installed
  | decode_stateless_input => exact DecodeStatelessInput.preserves cursor code installed
  | input_blob => exact InputBlob.preserves cursor code installed
  | host_input_byte => exact HostInputByte.preserves cursor code installed
  | host_input_le32 => exact HostInputLe32.preserves cursor code installed
  | precheck_host_ssz_header => exact PrecheckHostSszHeader.preserves cursor code installed
  | decode_host_input => exact DecodeHostInput.preserves cursor code installed
  | st_le32 => exact StLe32.preserves cursor code installed
  | st_le64 => exact StLe64.preserves cursor code installed
  | serialize_result => exact SerializeResult.preserves cursor code installed
  | output_write => exact OutputWrite.preserves cursor code installed

theorem call_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (routine : Code.Routine)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves (key cursor) code (.call (GlobalEffects.callInfo destination) (Code.name routine) arguments) :=
  GlobalEffects.call_body (key cursor) code destination (Code.name routine) arguments
    (Code.formals routine) (Code.body routine) (Code.shape routine)
    (Code.installed code installed routine) (body_preserves cursor code installed routine)

end Effects
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.Effects.body_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.Effects.call_preserves
