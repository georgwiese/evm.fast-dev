import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace Code
inductive Routine where
  | trap_with
  | alloc
  | sha256_init
  | keccak_init
  | ssz_init
  | keccak_f1600
  | keccak_absorb_block
  | memcpy
  | memzero
  | keccak256
  | mpt_init
  | u256_ws_init
  | secp256k1_init
  | bn254_init
  | bls_consts_init
  | bls_lib_init
  | bls_precompiles_init
  | ripemd160_init
  | blake2_init
  | header_init
  | heap_mark
  | heap_release
  | evm_init
  | st_be32
  | bswap64
  | st_be64
  | addr_from_words
  | fork_init
  | ssz_fail
  | ssz_split_var_list
  | decode_bytes_list
  | ssz_check_offsets
  | udivmod
  | ssz_fixed_list_count
  | decode_payload
  | decode_requests
  | decode_stateless_input
  | input_blob
  | host_input_byte
  | host_input_le32
  | precheck_host_ssz_header
  | decode_host_input
  | st_le32
  | st_le64
  | serialize_result
  | output_write

def declaration : Routine → Decl (BitVec 64)
  | .trap_with => Guest.Software.guestFn_trap_with
  | .alloc => Guest.Software.guestFn_alloc
  | .sha256_init => Guest.Software.guestFn_sha256_init
  | .keccak_init => Guest.Software.guestFn_keccak_init
  | .ssz_init => Guest.Software.guestFn_ssz_init
  | .keccak_f1600 => Guest.Software.guestFn_keccak_f1600
  | .keccak_absorb_block => Guest.Software.guestFn_keccak_absorb_block
  | .memcpy => Guest.Software.guestFn_memcpy
  | .memzero => Guest.Software.guestFn_memzero
  | .keccak256 => Guest.Software.guestFn_keccak256
  | .mpt_init => Guest.Software.guestFn_mpt_init
  | .u256_ws_init => Guest.Software.guestFn_u256_ws_init
  | .secp256k1_init => Guest.Software.guestFn_secp256k1_init
  | .bn254_init => Guest.Software.guestFn_bn254_init
  | .bls_consts_init => Guest.Software.guestFn_bls_consts_init
  | .bls_lib_init => Guest.Software.guestFn_bls_lib_init
  | .bls_precompiles_init => Guest.Software.guestFn_bls_precompiles_init
  | .ripemd160_init => Guest.Software.guestFn_ripemd160_init
  | .blake2_init => Guest.Software.guestFn_blake2_init
  | .header_init => Guest.Software.guestFn_header_init
  | .heap_mark => Guest.Software.guestFn_heap_mark
  | .heap_release => Guest.Software.guestFn_heap_release
  | .evm_init => Guest.Software.guestFn_evm_init
  | .st_be32 => Guest.Software.guestFn_st_be32
  | .bswap64 => Guest.Software.guestFn_bswap64
  | .st_be64 => Guest.Software.guestFn_st_be64
  | .addr_from_words => Guest.Software.guestFn_addr_from_words
  | .fork_init => Guest.Software.guestFn_fork_init
  | .ssz_fail => Guest.Software.guestFn_ssz_fail
  | .ssz_split_var_list => Guest.Software.guestFn_ssz_split_var_list
  | .decode_bytes_list => Guest.Software.guestFn_decode_bytes_list
  | .ssz_check_offsets => Guest.Software.guestFn_ssz_check_offsets
  | .udivmod => Guest.Software.guestFn_udivmod
  | .ssz_fixed_list_count => Guest.Software.guestFn_ssz_fixed_list_count
  | .decode_payload => Guest.Software.guestFn_decode_payload
  | .decode_requests => Guest.Software.guestFn_decode_requests
  | .decode_stateless_input => Guest.Software.guestFn_decode_stateless_input
  | .input_blob => Guest.Software.guestFn_input_blob
  | .host_input_byte => Guest.Software.guestFn_host_input_byte
  | .host_input_le32 => Guest.Software.guestFn_host_input_le32
  | .precheck_host_ssz_header => Guest.Software.guestFn_precheck_host_ssz_header
  | .decode_host_input => Guest.Software.guestFn_decode_host_input
  | .st_le32 => Guest.Software.guestFn_st_le32
  | .st_le64 => Guest.Software.guestFn_st_le64
  | .serialize_result => Guest.Software.guestFn_serialize_result
  | .output_write => Guest.Software.guestFn_output_write

def entry (routine : Routine) := GasBudget.OriginalCodeEnvironment.originalEntry (declaration routine)
def name : Routine → MlS
  | .trap_with => ofString "trap_with"
  | .alloc => ofString "alloc"
  | .sha256_init => ofString "sha256_init"
  | .keccak_init => ofString "keccak_init"
  | .ssz_init => ofString "ssz_init"
  | .keccak_f1600 => ofString "keccak_f1600"
  | .keccak_absorb_block => ofString "keccak_absorb_block"
  | .memcpy => ofString "memcpy"
  | .memzero => ofString "memzero"
  | .keccak256 => ofString "keccak256"
  | .mpt_init => ofString "mpt_init"
  | .u256_ws_init => ofString "u256_ws_init"
  | .secp256k1_init => ofString "secp256k1_init"
  | .bn254_init => ofString "bn254_init"
  | .bls_consts_init => ofString "bls_consts_init"
  | .bls_lib_init => ofString "bls_lib_init"
  | .bls_precompiles_init => ofString "bls_precompiles_init"
  | .ripemd160_init => ofString "ripemd160_init"
  | .blake2_init => ofString "blake2_init"
  | .header_init => ofString "header_init"
  | .heap_mark => ofString "heap_mark"
  | .heap_release => ofString "heap_release"
  | .evm_init => ofString "evm_init"
  | .st_be32 => ofString "st_be32"
  | .bswap64 => ofString "bswap64"
  | .st_be64 => ofString "st_be64"
  | .addr_from_words => ofString "addr_from_words"
  | .fork_init => ofString "fork_init"
  | .ssz_fail => ofString "ssz_fail"
  | .ssz_split_var_list => ofString "ssz_split_var_list"
  | .decode_bytes_list => ofString "decode_bytes_list"
  | .ssz_check_offsets => ofString "ssz_check_offsets"
  | .udivmod => ofString "udivmod"
  | .ssz_fixed_list_count => ofString "ssz_fixed_list_count"
  | .decode_payload => ofString "decode_payload"
  | .decode_requests => ofString "decode_requests"
  | .decode_stateless_input => ofString "decode_stateless_input"
  | .input_blob => ofString "input_blob"
  | .host_input_byte => ofString "host_input_byte"
  | .host_input_le32 => ofString "host_input_le32"
  | .precheck_host_ssz_header => ofString "precheck_host_ssz_header"
  | .decode_host_input => ofString "decode_host_input"
  | .st_le32 => ofString "st_le32"
  | .st_le64 => ofString "st_le64"
  | .serialize_result => ofString "serialize_result"
  | .output_write => ofString "output_write"

def formals (routine : Routine) := (entry routine).2.1
def body (routine : Routine) := (entry routine).2.2.1
def shape (routine : Routine) := (entry routine).2.2.2

set_option maxRecDepth 100000 in
theorem installed (code) (installed : OriginalCode.Installed code) (routine : Routine) :
    code.lookup (name routine) = some (formals routine, body routine, shape routine) := by
  cases routine with
  | trap_with => exact OriginalCode.indexed code installed 0 (entry .trap_with) (by rfl)
  | alloc => exact OriginalCode.indexed code installed 2 (entry .alloc) (by rfl)
  | sha256_init => exact OriginalCode.indexed code installed 83 (entry .sha256_init) (by rfl)
  | keccak_init => exact OriginalCode.indexed code installed 89 (entry .keccak_init) (by rfl)
  | ssz_init => exact OriginalCode.indexed code installed 168 (entry .ssz_init) (by rfl)
  | keccak_f1600 => exact OriginalCode.indexed code installed 90 (entry .keccak_f1600) (by rfl)
  | keccak_absorb_block => exact OriginalCode.indexed code installed 91 (entry .keccak_absorb_block) (by rfl)
  | memcpy => exact OriginalCode.indexed code installed 11 (entry .memcpy) (by rfl)
  | memzero => exact OriginalCode.indexed code installed 12 (entry .memzero) (by rfl)
  | keccak256 => exact OriginalCode.indexed code installed 92 (entry .keccak256) (by rfl)
  | mpt_init => exact OriginalCode.indexed code installed 221 (entry .mpt_init) (by rfl)
  | u256_ws_init => exact OriginalCode.indexed code installed 32 (entry .u256_ws_init) (by rfl)
  | secp256k1_init => exact OriginalCode.indexed code installed 135 (entry .secp256k1_init) (by rfl)
  | bn254_init => exact OriginalCode.indexed code installed 591 (entry .bn254_init) (by rfl)
  | bls_consts_init => exact OriginalCode.indexed code installed 638 (entry .bls_consts_init) (by rfl)
  | bls_lib_init => exact OriginalCode.indexed code installed 743 (entry .bls_lib_init) (by rfl)
  | bls_precompiles_init => exact OriginalCode.indexed code installed 752 (entry .bls_precompiles_init) (by rfl)
  | ripemd160_init => exact OriginalCode.indexed code installed 560 (entry .ripemd160_init) (by rfl)
  | blake2_init => exact OriginalCode.indexed code installed 566 (entry .blake2_init) (by rfl)
  | header_init => exact OriginalCode.indexed code installed 218 (entry .header_init) (by rfl)
  | heap_mark => exact OriginalCode.indexed code installed 3 (entry .heap_mark) (by rfl)
  | heap_release => exact OriginalCode.indexed code installed 4 (entry .heap_release) (by rfl)
  | evm_init => exact OriginalCode.indexed code installed 518 (entry .evm_init) (by rfl)
  | st_be32 => exact OriginalCode.indexed code installed 22 (entry .st_be32) (by rfl)
  | bswap64 => exact OriginalCode.indexed code installed 18 (entry .bswap64) (by rfl)
  | st_be64 => exact OriginalCode.indexed code installed 23 (entry .st_be64) (by rfl)
  | addr_from_words => exact OriginalCode.indexed code installed 785 (entry .addr_from_words) (by rfl)
  | fork_init => exact OriginalCode.indexed code installed 786 (entry .fork_init) (by rfl)
  | ssz_fail => exact OriginalCode.indexed code installed 179 (entry .ssz_fail) (by rfl)
  | ssz_split_var_list => exact OriginalCode.indexed code installed 185 (entry .ssz_split_var_list) (by rfl)
  | decode_bytes_list => exact OriginalCode.indexed code installed 189 (entry .decode_bytes_list) (by rfl)
  | ssz_check_offsets => exact OriginalCode.indexed code installed 184 (entry .ssz_check_offsets) (by rfl)
  | udivmod => exact OriginalCode.indexed code installed 28 (entry .udivmod) (by rfl)
  | ssz_fixed_list_count => exact OriginalCode.indexed code installed 186 (entry .ssz_fixed_list_count) (by rfl)
  | decode_payload => exact OriginalCode.indexed code installed 187 (entry .decode_payload) (by rfl)
  | decode_requests => exact OriginalCode.indexed code installed 188 (entry .decode_requests) (by rfl)
  | decode_stateless_input => exact OriginalCode.indexed code installed 190 (entry .decode_stateless_input) (by rfl)
  | input_blob => exact OriginalCode.indexed code installed 24 (entry .input_blob) (by rfl)
  | host_input_byte => exact OriginalCode.indexed code installed 180 (entry .host_input_byte) (by rfl)
  | host_input_le32 => exact OriginalCode.indexed code installed 181 (entry .host_input_le32) (by rfl)
  | precheck_host_ssz_header => exact OriginalCode.indexed code installed 182 (entry .precheck_host_ssz_header) (by rfl)
  | decode_host_input => exact OriginalCode.indexed code installed 183 (entry .decode_host_input) (by rfl)
  | st_le32 => exact OriginalCode.indexed code installed 20 (entry .st_le32) (by rfl)
  | st_le64 => exact OriginalCode.indexed code installed 21 (entry .st_le64) (by rfl)
  | serialize_result => exact OriginalCode.indexed code installed 202 (entry .serialize_result) (by rfl)
  | output_write => exact OriginalCode.indexed code installed 25 (entry .output_write) (by rfl)

end Code
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.Code.installed
