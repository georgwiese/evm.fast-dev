import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.Input.CurrentRlp.Code
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Only the actual unchanged software RLP/helper declarations. This small
catalogue does not import a hypothetical complete writer or block execution. -/
inductive Fn where
  | heapMark | heapRelease | limb | bitLength | wideBits | wideBytes | wideMin
  | beLength | putBe | writeHeader | headerLength | writeBytes | writeWord | writeList
  | bytesLength | listLength | wordLength | writeWide | header | withdrawalLength | blockLength
  deriving DecidableEq

def declaration : Fn→Decl (BitVec 64)
  | .heapMark=>Guest.Software.guestFn_heap_mark
  | .heapRelease=>Guest.Software.guestFn_heap_release
  | .limb=>Guest.Software.guestFn_u256_limb
  | .bitLength=>Guest.Software.guestFn_bit_length64
  | .wideBits=>Guest.Software.guestFn_u256_bit_length
  | .wideBytes=>Guest.Software.guestFn_u256_byte_length
  | .wideMin=>Guest.Software.guestFn_u256_to_be_min
  | .beLength=>Guest.Software.guestFn_rlp_be_len
  | .putBe=>Guest.Software.guestFn_rlp_put_be
  | .writeHeader=>Guest.Software.guestFn_rlp_write_header
  | .headerLength=>Guest.Software.guestFn_rlp_header_len
  | .writeBytes=>Guest.Software.guestFn_rlp_encode_bytes
  | .writeWord=>Guest.Software.guestFn_rlp_encode_word
  | .writeList=>Guest.Software.guestFn_rlp_encode_list_header
  | .bytesLength=>Guest.Software.guestFn_rlp_bytes_encoded_len
  | .listLength=>Guest.Software.guestFn_rlp_list_header_len
  | .wordLength=>Guest.Software.guestFn_rlp_word_encoded_len
  | .writeWide=>Guest.Software.guestFn_rlp_put_u256
  | .header=>Guest.Software.guestFn_encode_header
  | .withdrawalLength=>Guest.Software.guestFn_withdrawal_rlp_len
  | .blockLength=>Guest.Software.guestFn_block_rlp_length

def index : Fn→Nat
  | .heapMark=>3 | .heapRelease=>4 | .limb=>37 | .bitLength=>71 | .wideBits=>72 | .wideBytes=>73 | .wideMin=>82
  | .beLength=>106 | .putBe=>107 | .writeHeader=>108 | .headerLength=>109 | .writeBytes=>110 | .writeWord=>111 | .writeList=>112
  | .bytesLength=>113 | .listLength=>114 | .wordLength=>115 | .writeWide=>209 | .header=>210 | .withdrawalLength=>778 | .blockLength=>787

def entry (function : Fn):=GasBudget.OriginalCodeEnvironment.originalEntry (declaration function)
def name (function : Fn):=(entry function).1
def formals (function : Fn):=(entry function).2.1
def body (function : Fn):=(entry function).2.2.1
def shape (function : Fn):=(entry function).2.2.2

set_option maxRecDepth 100000 in
theorem installed (code) (ready : OriginalCode.Installed code) (function : Fn) :
    code.lookup (name function)=some (formals function,body function,shape function) := by
  exact OriginalCode.indexed code ready (index function) (entry function) (by cases function <;> rfl)


/-- A concrete helper ABI/body view is accepted only by equality with its
actual software declaration. This avoids importing a larger code catalogue. -/
theorem installed_as (code) (ready : OriginalCode.Installed code) (function : Fn)
    {functionName : MlS} {parameters : List (MlS×ShapeHOL)} {program : ProgHOL 64} {resultShape : ShapeHOL}
    (expected : entry function=(functionName,parameters,program,resultShape)) :
    code.lookup functionName=some (parameters,program,resultShape) := by
  have known:=installed code ready function
  change code.lookup (entry function).1=some (entry function).2 at known
  rw [expected] at known
  exact known

end InitECandidate.Solver.Input.CurrentRlp.Code

#print axioms InitECandidate.Solver.Input.CurrentRlp.Code.installed

#print axioms InitECandidate.Solver.Input.CurrentRlp.Code.installed_as
