import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace Code
inductive Routine where
  | trap_with
  | alloc
  | heap_mark
  | heap_release
  | ceil_log2
  | max
  | memcpy
  | memzero
  | sha256_pair
  | merkleize
  | st_le32
  | st_le64
  | mix_in_length
  | pack_bytes
  | htr_bytes_list
  | htr_bytes_vector
  | merkleize_progressive
  | htr_plist_chunks
  | htr_pbytes
  | htr_pcontainer
  | htr_u64_at
  | htr_withdrawal
  | htr_payload
  | htr_bdep
  | htr_bexit
  | htr_cons
  | htr_deposit
  | htr_wdreq
  | htr_request_list
  | htr_requests
  | htr_new_payload_request

def declaration : Routine → Decl (BitVec 64)
  | .trap_with => Guest.Software.guestFn_trap_with
  | .alloc => Guest.Software.guestFn_alloc
  | .heap_mark => Guest.Software.guestFn_heap_mark
  | .heap_release => Guest.Software.guestFn_heap_release
  | .ceil_log2 => Guest.Software.guestFn_ceil_log2
  | .max => Guest.Software.guestFn_max
  | .memcpy => Guest.Software.guestFn_memcpy
  | .memzero => Guest.Software.guestFn_memzero
  | .sha256_pair => Guest.Software.guestFn_sha256_pair
  | .merkleize => Guest.Software.guestFn_merkleize
  | .st_le32 => Guest.Software.guestFn_st_le32
  | .st_le64 => Guest.Software.guestFn_st_le64
  | .mix_in_length => Guest.Software.guestFn_mix_in_length
  | .pack_bytes => Guest.Software.guestFn_pack_bytes
  | .htr_bytes_list => Guest.Software.guestFn_htr_bytes_list
  | .htr_bytes_vector => Guest.Software.guestFn_htr_bytes_vector
  | .merkleize_progressive => Guest.Software.guestFn_merkleize_progressive
  | .htr_plist_chunks => Guest.Software.guestFn_htr_plist_chunks
  | .htr_pbytes => Guest.Software.guestFn_htr_pbytes
  | .htr_pcontainer => Guest.Software.guestFn_htr_pcontainer
  | .htr_u64_at => Guest.Software.guestFn_htr_u64_at
  | .htr_withdrawal => Guest.Software.guestFn_htr_withdrawal
  | .htr_payload => Guest.Software.guestFn_htr_payload
  | .htr_bdep => Guest.Software.guestFn_htr_bdep
  | .htr_bexit => Guest.Software.guestFn_htr_bexit
  | .htr_cons => Guest.Software.guestFn_htr_cons
  | .htr_deposit => Guest.Software.guestFn_htr_deposit
  | .htr_wdreq => Guest.Software.guestFn_htr_wdreq
  | .htr_request_list => Guest.Software.guestFn_htr_request_list
  | .htr_requests => Guest.Software.guestFn_htr_requests
  | .htr_new_payload_request => Guest.Software.guestFn_htr_new_payload_request

def entry (routine : Routine) := GasBudget.OriginalCodeEnvironment.originalEntry (declaration routine)
def name : Routine → MlS
  | .trap_with => ofString "trap_with"
  | .alloc => ofString "alloc"
  | .heap_mark => ofString "heap_mark"
  | .heap_release => ofString "heap_release"
  | .ceil_log2 => ofString "ceil_log2"
  | .max => ofString "max"
  | .memcpy => ofString "memcpy"
  | .memzero => ofString "memzero"
  | .sha256_pair => ofString "sha256_pair"
  | .merkleize => ofString "merkleize"
  | .st_le32 => ofString "st_le32"
  | .st_le64 => ofString "st_le64"
  | .mix_in_length => ofString "mix_in_length"
  | .pack_bytes => ofString "pack_bytes"
  | .htr_bytes_list => ofString "htr_bytes_list"
  | .htr_bytes_vector => ofString "htr_bytes_vector"
  | .merkleize_progressive => ofString "merkleize_progressive"
  | .htr_plist_chunks => ofString "htr_plist_chunks"
  | .htr_pbytes => ofString "htr_pbytes"
  | .htr_pcontainer => ofString "htr_pcontainer"
  | .htr_u64_at => ofString "htr_u64_at"
  | .htr_withdrawal => ofString "htr_withdrawal"
  | .htr_payload => ofString "htr_payload"
  | .htr_bdep => ofString "htr_bdep"
  | .htr_bexit => ofString "htr_bexit"
  | .htr_cons => ofString "htr_cons"
  | .htr_deposit => ofString "htr_deposit"
  | .htr_wdreq => ofString "htr_wdreq"
  | .htr_request_list => ofString "htr_request_list"
  | .htr_requests => ofString "htr_requests"
  | .htr_new_payload_request => ofString "htr_new_payload_request"

def formals (routine : Routine) := (entry routine).2.1
def body (routine : Routine) := (entry routine).2.2.1
def shape (routine : Routine) := (entry routine).2.2.2

set_option maxRecDepth 100000 in
theorem installed (code) (installed : OriginalCode.Installed code) (routine : Routine) :
    code.lookup (name routine) = some (formals routine, body routine, shape routine) := by
  cases routine with
  | trap_with => exact OriginalCode.indexed code installed 0 (entry .trap_with) (by rfl)
  | alloc => exact OriginalCode.indexed code installed 2 (entry .alloc) (by rfl)
  | heap_mark => exact OriginalCode.indexed code installed 3 (entry .heap_mark) (by rfl)
  | heap_release => exact OriginalCode.indexed code installed 4 (entry .heap_release) (by rfl)
  | ceil_log2 => exact OriginalCode.indexed code installed 31 (entry .ceil_log2) (by rfl)
  | max => exact OriginalCode.indexed code installed 27 (entry .max) (by rfl)
  | memcpy => exact OriginalCode.indexed code installed 11 (entry .memcpy) (by rfl)
  | memzero => exact OriginalCode.indexed code installed 12 (entry .memzero) (by rfl)
  | sha256_pair => exact OriginalCode.indexed code installed 88 (entry .sha256_pair) (by rfl)
  | merkleize => exact OriginalCode.indexed code installed 169 (entry .merkleize) (by rfl)
  | st_le32 => exact OriginalCode.indexed code installed 20 (entry .st_le32) (by rfl)
  | st_le64 => exact OriginalCode.indexed code installed 21 (entry .st_le64) (by rfl)
  | mix_in_length => exact OriginalCode.indexed code installed 170 (entry .mix_in_length) (by rfl)
  | pack_bytes => exact OriginalCode.indexed code installed 175 (entry .pack_bytes) (by rfl)
  | htr_bytes_list => exact OriginalCode.indexed code installed 177 (entry .htr_bytes_list) (by rfl)
  | htr_bytes_vector => exact OriginalCode.indexed code installed 176 (entry .htr_bytes_vector) (by rfl)
  | merkleize_progressive => exact OriginalCode.indexed code installed 171 (entry .merkleize_progressive) (by rfl)
  | htr_plist_chunks => exact OriginalCode.indexed code installed 172 (entry .htr_plist_chunks) (by rfl)
  | htr_pbytes => exact OriginalCode.indexed code installed 173 (entry .htr_pbytes) (by rfl)
  | htr_pcontainer => exact OriginalCode.indexed code installed 174 (entry .htr_pcontainer) (by rfl)
  | htr_u64_at => exact OriginalCode.indexed code installed 178 (entry .htr_u64_at) (by rfl)
  | htr_withdrawal => exact OriginalCode.indexed code installed 191 (entry .htr_withdrawal) (by rfl)
  | htr_payload => exact OriginalCode.indexed code installed 193 (entry .htr_payload) (by rfl)
  | htr_bdep => exact OriginalCode.indexed code installed 197 (entry .htr_bdep) (by rfl)
  | htr_bexit => exact OriginalCode.indexed code installed 198 (entry .htr_bexit) (by rfl)
  | htr_cons => exact OriginalCode.indexed code installed 196 (entry .htr_cons) (by rfl)
  | htr_deposit => exact OriginalCode.indexed code installed 194 (entry .htr_deposit) (by rfl)
  | htr_wdreq => exact OriginalCode.indexed code installed 195 (entry .htr_wdreq) (by rfl)
  | htr_request_list => exact OriginalCode.indexed code installed 199 (entry .htr_request_list) (by rfl)
  | htr_requests => exact OriginalCode.indexed code installed 200 (entry .htr_requests) (by rfl)
  | htr_new_payload_request => exact OriginalCode.indexed code installed 201 (entry .htr_new_payload_request) (by rfl)

end Code
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.Code.installed
