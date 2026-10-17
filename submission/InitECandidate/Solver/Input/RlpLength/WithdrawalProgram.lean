import InitECandidate.Solver.Input.RlpLength.ListHeader
import InitECandidate.Solver.Input.HeapFlatScalar

namespace InitECandidate.Solver.Input.RlpLength.Withdrawal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_withdrawal_rlp_len with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "wd",.one)]
def firstExpression : ExpHOL 64 := Scalar.flat64 (localVar "wd") []
def secondExpression : ExpHOL 64 := Scalar.flat64 (localVar "wd") [8]
def thirdExpression : ExpHOL 64 := Scalar.flat64 (localVar "wd") [36]
def payloadExpression : ExpHOL 64 := .op .add [localVar "a",localVar "b",.const 21#64,localVar "c"]
def returnLength : ProgHOL 64 := .return (.op .add [localVar "payload",localVar "hl"])
def payloadTail : ProgHOL 64 := .decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload"] returnLength
def afterC : ProgHOL 64 := .dec (ofString "payload") .one payloadExpression payloadTail
def afterB : ProgHOL 64 := .decCall (ofString "c") .one (ofString "rlp_word_encoded_len") [thirdExpression] afterC
def afterA : ProgHOL 64 := .decCall (ofString "b") .one (ofString "rlp_word_encoded_len") [secondExpression] afterB

theorem body_shape : body=.decCall (ofString "a") .one (ofString "rlp_word_encoded_len") [firstExpression] afterA := by
  simp only [body,Guest.guestFn_withdrawal_rlp_len,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    firstExpression,secondExpression,thirdExpression,payloadExpression,returnLength,payloadTail,afterC,afterB,afterA,
    Scalar.flat64,Scalar.flat32,Scalar.flatAddress,Scalar.shift,localVar,List.nil_append,List.cons_append,List.append_nil]

theorem scalar_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (start offset : Nat) (heap : Blob.HeapInput source input pointer) (inside : start+offset+8≤input.length%2^64)
    (wd : source.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start)))) :
    eval source (Scalar.flat64 (localVar "wd") (if offset=0 then [] else [offset]))=
      some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+offset))))) := by
  have baseRead : eval source (localVar "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using wd
  by_cases zero : offset=0
  · subst offset
    simp only [if_pos rfl,Nat.add_zero] at *
    exact Scalar.flat_heap_le64 source input pointer (pointer+BitVec.ofNat 64 start) (localVar "wd") [] start heap inside baseRead (by simp)
  · simp only [if_neg zero]
    exact Scalar.flat_heap_le64 source input pointer (pointer+BitVec.ofNat 64 start) (localVar "wd") [offset] (start+offset) heap inside baseRead
      (by simp [BitVec.ofNat_add,BitVec.add_assoc])

theorem singleton_args (source : PanSemStateFiniteExact 64 Guest.HostMemory) (expression : ExpHOL 64) (value : BitVec 64)
    (read : eval source expression=some (.val (.word value))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [expression]=some [.val (.word value)] := by
  simp only [eval] at read
  simp [evalListHOLFinite,evalListHOLExact,read]

end InitECandidate.Solver.Input.RlpLength.Withdrawal

#print axioms InitECandidate.Solver.Input.RlpLength.Withdrawal.body_shape
#print axioms InitECandidate.Solver.Input.RlpLength.Withdrawal.scalar_read
