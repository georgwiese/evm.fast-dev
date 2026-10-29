import InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore

namespace InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

-- Preserve the seven-key public API. The shared ten-key proofs live in the core;
-- mpt_init has its own restricted proof because it initializes the MPT workspace keys.

theorem trap_with (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .trap_with) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.trap_with code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem alloc (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .alloc) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.alloc code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem keccak_f1600 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .keccak_f1600) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.keccak_f1600 code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem keccak_absorb_block (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .keccak_absorb_block) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.keccak_absorb_block code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem memcpy (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .memcpy) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.memcpy code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem memzero (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .memzero) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.memzero code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem keccak256 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .keccak256) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.keccak256 code installed (WorkspaceFrameCore.fromLegacy workspace)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem mpt_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .mpt_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_mpt_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (keccak256 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (keccak256 code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _)))))))))


theorem u256_ws_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .u256_ws_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.u256_ws_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem secp256k1_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .secp256k1_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.secp256k1_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem bn254_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bn254_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.bn254_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem bls_consts_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bls_consts_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.bls_consts_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem bls_lib_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bls_lib_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.bls_lib_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem bls_precompiles_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bls_precompiles_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.bls_precompiles_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem ripemd160_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ripemd160_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.ripemd160_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem blake2_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .blake2_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.blake2_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem header_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .header_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.header_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem heap_mark (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .heap_mark) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.heap_mark code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem heap_release (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .heap_release) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.heap_release code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem evm_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .evm_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.evm_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem st_be32 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .st_be32) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.st_be32 code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem bswap64 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bswap64) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.bswap64 code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem st_be64 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .st_be64) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.st_be64 code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem addr_from_words (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .addr_from_words) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.addr_from_words code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem fork_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .fork_init) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.fork_init code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem ssz_fail (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ssz_fail) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.ssz_fail code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem ssz_split_var_list (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ssz_split_var_list) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.ssz_split_var_list code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem decode_bytes_list (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_bytes_list) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.decode_bytes_list code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem ssz_check_offsets (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ssz_check_offsets) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.ssz_check_offsets code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem udivmod (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .udivmod) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.udivmod code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem ssz_fixed_list_count (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ssz_fixed_list_count) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.ssz_fixed_list_count code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem decode_payload (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_payload) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.decode_payload code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem decode_requests (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_requests) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.decode_requests code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem decode_stateless_input (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_stateless_input) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.decode_stateless_input code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem input_blob (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .input_blob) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.input_blob code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem host_input_byte (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .host_input_byte) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.host_input_byte code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem host_input_le32 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .host_input_le32) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.host_input_le32 code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem precheck_host_ssz_header (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .precheck_host_ssz_header) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.precheck_host_ssz_header code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem decode_host_input (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_host_input) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.decode_host_input code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem st_le32 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .st_le32) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.st_le32 code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem st_le64 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .st_le64) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.st_le64 code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem serialize_result (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .serialize_result) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.serialize_result code installed (WorkspaceFrameCore.fromLegacy workspace)

theorem output_write (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .output_write) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.output_write code installed (WorkspaceFrameCore.fromLegacy workspace)

end InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame


#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.trap_with
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.alloc
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.keccak_f1600
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.keccak_absorb_block
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.memcpy
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.memzero
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.keccak256
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.mpt_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.u256_ws_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.secp256k1_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.bn254_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.bls_consts_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.bls_lib_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.bls_precompiles_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.ripemd160_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.blake2_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.header_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.heap_mark
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.heap_release
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.evm_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.st_be32
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.bswap64
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.st_be64
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.addr_from_words
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.fork_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.ssz_fail
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.ssz_split_var_list
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.decode_bytes_list
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.ssz_check_offsets
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.udivmod
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.ssz_fixed_list_count
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.decode_payload
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.decode_requests
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.decode_stateless_input
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.input_blob
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.host_input_byte
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.host_input_le32
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.precheck_host_ssz_header
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.decode_host_input
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.st_le32
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.st_le64
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.serialize_result
#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.output_write
