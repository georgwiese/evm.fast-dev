import InitECandidate.Solver.Input.HeapFlatScalar
import InitECandidate.Solver.WitnessRadix.AllocatedArena
import InitECandidate.Solver.Input.HeaderProgram
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

def body : ProgHOL 64 := match Guest.Software.guestFn_decode_requests with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "p",.one),(ofString "len",.one)]
def shortTest : ExpHOL 64 := .cmp .lower (localVar "len") (.const 20#64)
def shortGuard : ProgHOL 64 := .ite shortTest (.call (some (none,none)) (ofString "ssz_fail") [.const 60#64]) .skip
def offsetTail : ProgHOL 64 := match body with | .seq _ (.dec _ _ _ (.seq _ rest)) => rest | _ => .skip
def offsetTest : ExpHOL 64:=.cmp .less (localVar "i") (.const 5#64)
def offsetAddress : ExpHOL 64:=.op .add [Header.offsets,.panop .mul [localVar "i",.const 8#64]]
def offsetInput : ExpHOL 64:=.op .add [localVar "p",.panop .mul [localVar "i",.const 4#64]]
def offsetByte (offset : Nat) : ExpHOL 64:=.op .add [localVar "p",.panop .mul [localVar "i",.const 4#64],.const (BitVec.ofNat 64 offset)]
def offsetRead : ExpHOL 64:=.op .or [.loadByte offsetInput,Scalar.shift (.loadByte (offsetByte 1)) 8,
  Scalar.shift (.loadByte (offsetByte 2)) 16,Scalar.shift (.loadByte (offsetByte 3)) 24]
def offsetStore : ProgHOL 64:=.store offsetAddress offsetRead
def offsetIncrement : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def offsetStep : ProgHOL 64:=.seq offsetStore offsetIncrement
def offsetLoop : ProgHOL 64:=.while offsetTest offsetStep
def offsetArguments : List (ExpHOL 64):=[Header.offsets,.const 5#64,.const 20#64,localVar "len"]
def offsetGuard : ProgHOL 64:=.call (some (none,none)) (ofString "ssz_check_offsets") offsetArguments

theorem body_shape : body = .seq shortGuard (.dec (ofString "i") .one (.const 0#64) (.seq offsetLoop offsetTail)) := by
  simp only [body,Guest.Software.guestFn_decode_requests,progToHOL,shortGuard,shortTest,offsetLoop,offsetTest,offsetStep,offsetStore,offsetIncrement,
    offsetAddress,offsetInput,offsetByte,offsetRead,offsetTail,shapeToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_none,Header.offsets,Scalar.shift,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "decode_requests") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 188 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_decode_requests) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_decode_requests,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def offsetWord (input : Guest.InputBlob) (start index : Nat) : BitVec 64:=
  BitVec.ofNat 64 (Guest.GasLimit.le32 input (start+4*index))

/-- Every actual loop iteration reads four bytes within the copied witness
prefix, independently of later schema validation. -/
theorem offset_input_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (start index : Nat) (heap : Blob.HeapInput source input pointer)
    (inside : start+4*index+4≤input.length%2^64)
    (wp : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
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

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.body_shape
#print axioms InitECandidate.Solver.Input.Requests.original_code
#print axioms InitECandidate.Solver.Input.Requests.offset_input_read
