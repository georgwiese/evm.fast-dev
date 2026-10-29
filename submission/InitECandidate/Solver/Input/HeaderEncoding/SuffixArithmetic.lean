import InitECandidate.Solver.Input.HeaderEncoding.FieldBounds
import InitECandidate.Solver.Input.RlpWrite.ListWrite
import InitECandidate.Solver.Input.RlpLength.ListHeader

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure TailCodes (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  listLength : source.code.lookup (ofString "rlp_list_header_len")=some (RlpLength.ListHeader.formals,RlpLength.ListHeader.body,.one)
  headerLength : source.code.lookup (ofString "rlp_header_len")=some (RlpLength.Header.formals,RlpLength.Header.body,.one)
  listWriter : source.code.lookup (ofString "rlp_encode_list_header")=some (RlpWrite.ListWrite.formals,RlpWrite.ListWrite.body,.one)

def afterStart : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "rlp_encode_list_header") [localVar "start",localVar "payload_len"]) returnHeader
def afterHeaderLength : ProgHOL 64 := .dec (ofString "start") .one startExpression afterStart
def encodedPair (pointer : BitVec 64) (length : Nat) : ValueHOL 64 := .rStruct [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))]

theorem suffix_shape : suffix=.dec (ofString "payload_len") .one payloadExpression
    (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload_len"] afterHeaderLength) := rfl

theorem payload_difference (header buffer : BitVec 64) (geometry : Geometry header buffer) (position : Nat) (lower : 9≤position) (upper : position≤916) :
    address buffer position-(buffer+9#64)=BitVec.ofNat 64 (position-9) := by
  have number:=geometry.position_number header buffer position (by omega)
  have baseNumber : (buffer+9#64).toNat=buffer.toNat+9:=geometry.position_number header buffer 9 (by decide)
  have ordered : buffer+9#64≤address buffer position := by change (buffer+9#64).toNat≤(address buffer position).toNat; rw [number,baseNumber]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le ordered,number,baseNumber,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

theorem start_difference (header buffer : BitVec 64) (geometry : Geometry header buffer) (length : Nat) (lower : 1≤length) (upper : length≤9) :
    (buffer+9#64)-BitVec.ofNat 64 length=address buffer (9-length) := by
  have number : (buffer+9#64).toNat=buffer.toNat+9:=geometry.position_number header buffer 9 (by decide)
  have lengthNumber : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have destination:=geometry.position_number header buffer (9-length) (by omega)
  have ordered : BitVec.ofNat 64 length≤buffer+9#64 := by change (BitVec.ofNat 64 length).toNat≤(buffer+9#64).toNat; rw [lengthNumber,number]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le ordered,number,lengthNumber,destination]
  omega

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.suffix_shape
#print axioms InitECandidate.Solver.Input.HeaderEncoding.payload_difference
#print axioms InitECandidate.Solver.Input.HeaderEncoding.start_difference
