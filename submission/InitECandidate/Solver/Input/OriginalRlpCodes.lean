import InitECandidate.Solver.Input.RlpLength.BlockGuard
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.WitnessRadix.AllocationEnvironment
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode

namespace InitECandidate.Solver.Input.OriginalRlp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem heap_mark (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "heap_mark")=some ([],HeapScope.markBody,.one) := by
  have checked:=OriginalCode.indexed code installed 3 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_heap_mark) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,HeapScope.markBody,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_heap_mark,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem heap_release (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "heap_release")=some (HeapScope.releaseFormals,HeapScope.releaseBody,.one) := by
  have checked:=OriginalCode.indexed code installed 4 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_heap_release) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,HeapScope.releaseFormals,HeapScope.releaseBody,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_heap_release,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem u256_limb (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "u256_limb")=some (RlpWrite.U256Limb.formals,RlpWrite.U256Limb.body,.one) := by
  have checked:=OriginalCode.indexed code installed 37 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_u256_limb) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.U256Limb.formals,RlpWrite.U256Limb.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_u256_limb,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem bit_length64 (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "bit_length64")=some (RlpWrite.BitLength.formals,RlpWrite.BitLength.body,.one) := by
  have checked:=OriginalCode.indexed code installed 71 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_bit_length64) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.BitLength.formals,RlpWrite.BitLength.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_bit_length64,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem u256_bit_length (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "u256_bit_length")=some (RlpWrite.U256Bits.formals,RlpWrite.U256Bits.body,.one) := by
  have checked:=OriginalCode.indexed code installed 72 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_u256_bit_length) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.U256Bits.formals,RlpWrite.U256Bits.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_u256_bit_length,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem u256_byte_length (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "u256_byte_length")=some (RlpWrite.U256ByteLength.formals,RlpWrite.U256ByteLength.body,.one) := by
  have checked:=OriginalCode.indexed code installed 73 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_u256_byte_length) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.U256ByteLength.formals,RlpWrite.U256ByteLength.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_u256_byte_length,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem u256_to_be_min (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "u256_to_be_min")=some (RlpWrite.U256Min.formals,RlpWrite.U256Min.body,.one) := by
  have checked:=OriginalCode.indexed code installed 82 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_u256_to_be_min) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.U256Min.formals,RlpWrite.U256Min.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_u256_to_be_min,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_be_len (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one) := by
  have checked:=OriginalCode.indexed code installed 106 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_be_len) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpLength.Be.formals,RlpLength.Be.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_be_len,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_put_be (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_put_be")=some (RlpWrite.PutBe.formals,RlpWrite.PutBe.body,.one) := by
  have checked:=OriginalCode.indexed code installed 107 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_put_be) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.PutBe.formals,RlpWrite.PutBe.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_put_be,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_write_header (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_write_header")=some (RlpWrite.HeaderWrite.formals,RlpWrite.HeaderWrite.body,.one) := by
  have checked:=OriginalCode.indexed code installed 108 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_write_header) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.HeaderWrite.formals,RlpWrite.HeaderWrite.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_write_header,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_header_len (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_header_len")=some (RlpLength.Header.formals,RlpLength.Header.body,.one) := by
  have checked:=OriginalCode.indexed code installed 109 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_header_len) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpLength.Header.formals,RlpLength.Header.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_header_len,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_encode_bytes (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_encode_bytes")=some (RlpWrite.BytesWrite.formals,RlpWrite.BytesWrite.body,.one) := by
  have checked:=OriginalCode.indexed code installed 110 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_encode_bytes) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.BytesWrite.formals,RlpWrite.BytesWrite.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_encode_bytes,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_encode_word (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_encode_word")=some (RlpWrite.WordWrite.formals,RlpWrite.WordWrite.body,.one) := by
  have checked:=OriginalCode.indexed code installed 111 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_encode_word) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.WordWrite.formals,RlpWrite.WordWrite.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_encode_word,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_encode_list_header (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_encode_list_header")=some (RlpWrite.ListWrite.formals,RlpWrite.ListWrite.body,.one) := by
  have checked:=OriginalCode.indexed code installed 112 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_encode_list_header) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.ListWrite.formals,RlpWrite.ListWrite.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_encode_list_header,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_bytes_encoded_len (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_bytes_encoded_len")=some (RlpLength.BytesSize.formals,RlpLength.BytesSize.body,.one) := by
  have checked:=OriginalCode.indexed code installed 113 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_bytes_encoded_len) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpLength.BytesSize.formals,RlpLength.BytesSize.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_bytes_encoded_len,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_list_header_len (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_list_header_len")=some (RlpLength.ListHeader.formals,RlpLength.ListHeader.body,.one) := by
  have checked:=OriginalCode.indexed code installed 114 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_list_header_len) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpLength.ListHeader.formals,RlpLength.ListHeader.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_list_header_len,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_word_encoded_len (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_word_encoded_len")=some (RlpLength.WordSize.formals,RlpLength.WordSize.body,.one) := by
  have checked:=OriginalCode.indexed code installed 115 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_word_encoded_len) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpLength.WordSize.formals,RlpLength.WordSize.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_word_encoded_len,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem rlp_put_u256 (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_put_u256")=some (RlpWrite.U256Put.formals,RlpWrite.U256Put.body,.one) := by
  have checked:=OriginalCode.indexed code installed 211 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_put_u256) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpWrite.U256Put.formals,RlpWrite.U256Put.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_rlp_put_u256,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem encode_header (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "encode_header")=some (HeaderEncoding.formals,HeaderEncoding.body,HeaderEncoding.returnShape) := by
  have checked:=OriginalCode.indexed code installed 212 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_encode_header) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,HeaderEncoding.formals,HeaderEncoding.body,HeaderEncoding.returnShape,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_encode_header,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem withdrawal_rlp_len (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "withdrawal_rlp_len")=some (RlpLength.Withdrawal.formals,RlpLength.Withdrawal.body,.one) := by
  have checked:=OriginalCode.indexed code installed 790 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_withdrawal_rlp_len) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpLength.Withdrawal.formals,RlpLength.Withdrawal.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_withdrawal_rlp_len,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem block_rlp_length (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "block_rlp_length")=some (RlpLength.Block.formals,RlpLength.Block.body,.one) := by
  have checked:=OriginalCode.indexed code installed 799 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_block_rlp_length) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,RlpLength.Block.formals,RlpLength.Block.body,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_block_rlp_length,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem bytes_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    RlpWrite.BytesWrite.Codes source :=
  ⟨rlp_write_header source.code installed,rlp_be_len source.code installed,rlp_put_be source.code installed,
    WitnessRadix.CopyGeneral.original_code source.code installed⟩

theorem minimum_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    RlpWrite.U256Min.Codes source :=
  ⟨u256_byte_length source.code installed,u256_bit_length source.code installed,bit_length64 source.code installed,u256_limb source.code installed⟩

theorem wide_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    RlpWrite.U256Put.Codes source :=
  ⟨heap_mark source.code installed,WitnessRadix.PersistentAlloc.original_code source.code installed,u256_to_be_min source.code installed,
    minimum_codes source installed,rlp_encode_bytes source.code installed,bytes_codes source installed,heap_release source.code installed⟩

theorem header_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    HeaderEncoding.Codes source :=
  ⟨rlp_put_u256 source.code installed,wide_codes source installed,rlp_encode_word source.code installed⟩

theorem header_tail_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    HeaderEncoding.TailCodes source :=
  ⟨rlp_list_header_len source.code installed,rlp_header_len source.code installed,rlp_encode_list_header source.code installed⟩

theorem block_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    RlpLength.Block.Codes source :=
  ⟨encode_header source.code installed,header_codes source installed,header_tail_codes source installed,
    WitnessRadix.PersistentAlloc.original_code source.code installed,heap_mark source.code installed,heap_release source.code installed,
    rlp_bytes_encoded_len source.code installed,withdrawal_rlp_len source.code installed,rlp_word_encoded_len source.code installed⟩

end InitECandidate.Solver.Input.OriginalRlp

#print axioms InitECandidate.Solver.Input.OriginalRlp.heap_mark
#print axioms InitECandidate.Solver.Input.OriginalRlp.heap_release
#print axioms InitECandidate.Solver.Input.OriginalRlp.u256_limb
#print axioms InitECandidate.Solver.Input.OriginalRlp.bit_length64
#print axioms InitECandidate.Solver.Input.OriginalRlp.u256_bit_length
#print axioms InitECandidate.Solver.Input.OriginalRlp.u256_byte_length
#print axioms InitECandidate.Solver.Input.OriginalRlp.u256_to_be_min
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_be_len
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_put_be
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_write_header
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_header_len
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_encode_bytes
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_encode_word
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_encode_list_header
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_bytes_encoded_len
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_list_header_len
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_word_encoded_len
#print axioms InitECandidate.Solver.Input.OriginalRlp.rlp_put_u256
#print axioms InitECandidate.Solver.Input.OriginalRlp.encode_header
#print axioms InitECandidate.Solver.Input.OriginalRlp.withdrawal_rlp_len
#print axioms InitECandidate.Solver.Input.OriginalRlp.block_rlp_length
#print axioms InitECandidate.Solver.Input.OriginalRlp.bytes_codes
#print axioms InitECandidate.Solver.Input.OriginalRlp.minimum_codes
#print axioms InitECandidate.Solver.Input.OriginalRlp.wide_codes
#print axioms InitECandidate.Solver.Input.OriginalRlp.header_codes
#print axioms InitECandidate.Solver.Input.OriginalRlp.header_tail_codes
#print axioms InitECandidate.Solver.Input.OriginalRlp.block_codes

