import InitECandidate.Solver.Input.Witness.Program
import InitECandidate.Solver.Input.HeapFlatScalar

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
set_option maxRecDepth 10000

def prefixBody : ProgHOL 64:=Payload.dropLeading 30 Header.body
def offsetBody : ProgHOL 64:=Payload.dropLeading 3 prefixBody
def offsetTail : ProgHOL 64:=Payload.dropLeading 2 offsetBody
def loadedBody : ProgHOL 64:=Payload.dropLeading 1 offsetTail
def witnessPointer : ExpHOL 64:=.op .add [localVar "p",localVar "o_wit"]
def witnessLength : ExpHOL 64:=.op .sub [localVar "len",localVar "o_wit"]
def shortGuard : ProgHOL 64:=.ite (.cmp .lower (localVar "wlen") (.const 12#64))
  (.call (some (none,none)) (ofString "ssz_fail") [.const 82#64]) .skip
def offsetTest : ExpHOL 64:=.cmp .less (localVar "i") (.const 3#64)
def offsetAddress : ExpHOL 64:=.op .add [Header.offsets,.panop .mul [localVar "i",.const 8#64]]
def offsetInput : ExpHOL 64:=.op .add [localVar "wp",.panop .mul [localVar "i",.const 4#64]]
def offsetByte (offset : Nat) : ExpHOL 64:=.op .add [localVar "wp",.panop .mul [localVar "i",.const 4#64],.const (BitVec.ofNat 64 offset)]
def offsetRead : ExpHOL 64:=.op .or [.loadByte offsetInput,Scalar.shift (.loadByte (offsetByte 1)) 8,
  Scalar.shift (.loadByte (offsetByte 2)) 16,Scalar.shift (.loadByte (offsetByte 3)) 24]
def offsetStore : ProgHOL 64:=.store offsetAddress offsetRead
def offsetIncrement : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def offsetStep : ProgHOL 64:=.seq offsetStore offsetIncrement
def offsetLoop : ProgHOL 64:=.while offsetTest offsetStep
def offsetArguments : List (ExpHOL 64):=[Header.offsets,.const 3#64,.const 12#64,localVar "wlen"]
def offsetGuard : ProgHOL 64:=.call (some (none,none)) (ofString "ssz_check_offsets") offsetArguments

theorem offset_shapes :
    prefixBody=.dec (ofString "wp") .one witnessPointer (.dec (ofString "wlen") .one witnessLength (.seq shortGuard offsetBody)) ∧
    offsetBody=.dec (ofString "i") .one (.const 0#64) (.seq offsetLoop offsetTail) ∧
    offsetTail=.seq offsetGuard loadedBody ∧
    loadedBody=.dec (ofString "w0") .one (.load .one Header.offsets)
      (.dec (ofString "w1") .one (.load .one (Scalar.plus Header.offsets 8))
        (.dec (ofString "w2") .one (.load .one (Scalar.plus Header.offsets 16)) nodeCall)) := by
  simp only [prefixBody,offsetBody,offsetTail,loadedBody,nodeCall,Header.body,Guest.Software.guestFn_decode_stateless_input,
    Payload.dropLeading,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    witnessPointer,witnessLength,shortGuard,offsetLoop,offsetTest,offsetStep,offsetStore,offsetIncrement,
    offsetAddress,offsetInput,offsetRead,offsetByte,offsetGuard,offsetArguments,Header.offsets,Scalar.plus,Scalar.flat32,
    Scalar.flatAddress,Scalar.shift,localVar,List.nil_append,List.cons_append,List.append_nil]
  trivial

def offsetWord (input : Guest.InputBlob) (start index : Nat) : BitVec 64:=
  BitVec.ofNat 64 (Guest.GasLimit.le32 input (start+4*index))

/-- Every actual loop iteration reads four bytes within the copied witness
prefix, independently of later schema validation. -/
theorem offset_input_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (start index : Nat) (heap : Blob.HeapInput source input pointer)
    (inside : start+4*index+4≤input.length%2^64)
    (wp : source.locals.lookup (ofString "wp")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source offsetRead=some (.val (.word (offsetWord input start index))) := by
  have base : eval source offsetInput=some (.val (.word (pointer+BitVec.ofNat 64 (start+4*index)))) := by
    simp [eval,offsetInput,localVar,evalHOLExact,evalListHOLExact,toExact,wp,i,valueIsWord,valueWord,
      wordOpHOL,wordOp,panOpHOL,←BitVec.ofNat_mul,BitVec.add_assoc,BitVec.ofNat_add,Nat.mul_comm]
  have addressNext (offset : Nat) : eval source (offsetByte offset)=eval source (Scalar.plus offsetInput offset) := by
    simp [eval,offsetByte,offsetInput,Scalar.plus,localVar,evalHOLExact,evalListHOLExact,toExact,wp,i,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.add_assoc]
  have equivalent : eval source offsetRead=eval source (Scalar.le32 offsetInput) := by
    apply Scalar.op_congr
    exact .cons rfl
      (.cons (Scalar.shift_congr source _ _ 8 (Scalar.byte_congr source _ _ (addressNext 1)))
        (.cons (Scalar.shift_congr source _ _ 16 (Scalar.byte_congr source _ _ (addressNext 2)))
          (.cons (Scalar.shift_congr source _ _ 24 (Scalar.byte_congr source _ _ (addressNext 3))) .nil)))
  exact equivalent.trans (Scalar.heap_le32 source input pointer (start+4*index) _ heap inside base)

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.offset_shapes
#print axioms InitECandidate.Solver.Input.Witness.offset_input_read
