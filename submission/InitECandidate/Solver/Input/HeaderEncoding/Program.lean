import InitECandidate.Solver.Input.RlpWrite.U256PutCall
import InitECandidate.Solver.Input.RlpWrite.WordWriteCall

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_encode_header with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "h",.one)]
def returnShape : ShapeHOL := .comb [.one,.one]

inductive Field where
  | bytes (offset length : Nat)
  | scalar (offset : Nat)
  | wide (offset : Nat)
  | extra
  deriving DecidableEq

def loadOne (offset : Nat) : ExpHOL 64 := .load .one (.op .add [localVar "h",.const (BitVec.ofNat 64 offset)])
def loadWide (offset : Nat) : ExpHOL 64 := .load RlpWrite.U256Value.tupleShape (.op .add [localVar "h",.const (BitVec.ofNat 64 offset)])
def functionName : Field→String
  | .bytes _ _ | .extra=>"rlp_encode_bytes"
  | .scalar _=>"rlp_encode_word"
  | .wide _=>"rlp_put_u256"
def arguments : Field→List (ExpHOL 64)
  | .bytes offset length=>[localVar "p",loadOne offset,.const (BitVec.ofNat 64 length)]
  | .extra=>[localVar "p",loadOne 128,loadOne 136]
  | .scalar offset=>[localVar "p",loadOne offset]
  | .wide offset=>[localVar "p",loadWide offset]
def call (field : Field) : ProgHOL 64 :=
  .call (some (some (.local,ofString "w"),none)) (ofString (functionName field)) (arguments field)
def advanceExpression : ExpHOL 64 := .op .add [localVar "p",localVar "w"]
def advance : ProgHOL 64 := .assign .local (ofString "p") advanceExpression
def fields : List Field→ProgHOL 64→ProgHOL 64
  | [],tail=>tail
  | field::rest,tail=>.seq (call field) (.seq advance (fields rest tail))

def firstField : Field := .bytes 8 32
def baseRest : List Field := [
  .bytes 16 32,.bytes 24 20,.bytes 32 32,.bytes 40 32,.bytes 48 32,.bytes 56 256,
  .wide 64,.scalar 96,.scalar 104,.scalar 112,.scalar 120,.extra,.bytes 144 32,.bytes 152 8,
  .wide 160,.bytes 192 32,.scalar 200,.scalar 208,.bytes 216 32,.bytes 224 32]
def optionalFields : List Field := [.bytes 232 32,.scalar 240]
def optionalCode : ProgHOL 64 := fields [.bytes 232 32] (.seq (call (.scalar 240)) advance)
def currentTest : ExpHOL 64 := .cmp .notEqual (loadOne 0) (.const 0#64)
def payloadExpression : ExpHOL 64 := .op .sub [localVar "p",.op .add [localVar "buf",.const 9#64]]
def startExpression : ExpHOL 64 := .op .sub [.op .add [localVar "buf",.const 9#64],localVar "hl"]
def returnHeader : ProgHOL 64 := .return (.rstruct [localVar "start",.op .add [localVar "payload_len",localVar "hl"]])
def suffix : ProgHOL 64 := .dec (ofString "payload_len") .one payloadExpression
  (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload_len"]
    (.dec (ofString "start") .one startExpression
      (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header") [localVar "start",localVar "payload_len"]) returnHeader)))
def afterBase : ProgHOL 64 := .seq (.ite currentTest optionalCode .skip) suffix
def afterFirst : ProgHOL 64 := .seq advance (fields baseRest afterBase)
def afterPointer : ProgHOL 64 := .decCall (ofString "w") .one (ofString "rlp_encode_bytes") (arguments firstField) afterFirst
def afterBuffer : ProgHOL 64 := .dec (ofString "p") .one (.op .add [localVar "buf",.const 9#64]) afterPointer

theorem body_shape : body=.decCall (ofString "buf") .one (ofString "alloc") [.const 1024#64] afterBuffer := by
  simp only [body,Guest.guestFn_encode_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    afterBuffer,afterPointer,afterFirst,firstField,arguments,fields,baseRest,call,functionName,loadOne,loadWide,RlpWrite.U256Value.tupleShape,
    advance,advanceExpression,afterBase,currentTest,optionalCode,suffix,payloadExpression,startExpression,returnHeader,localVar]

def maxSize : Field→Nat
  | .bytes _ length=>length+9
  | .extra=>41
  | .scalar _=>9
  | .wide _=>41
def maxCost : Field→Nat
  | .bytes _ length=>length+21
  | .extra=>53
  | .scalar _=>19
  | .wide _=>125
def sizes (items : List Field) : Nat := (items.map maxSize).sum
def costs (items : List Field) : Nat := (items.map maxCost).sum

theorem literal_budgets : sizes (firstField::baseRest)=857 ∧ sizes optionalFields=50 ∧
    costs (firstField::baseRest)=1241 ∧ costs optionalFields=72 ∧ 857+50+9≤1024 := by decide

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.body_shape
#print axioms InitECandidate.Solver.Input.HeaderEncoding.literal_budgets
