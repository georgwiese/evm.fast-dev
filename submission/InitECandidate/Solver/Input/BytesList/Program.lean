import InitECandidate.Solver.Input.VarList.CallerNormal
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_decode_bytes_list with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "len",.one),(ofString "lim",.one),(ofString "maxb",.one)]
def arguments : List (ExpHOL 64) := [localVar "p",localVar "len",localVar "lim"]
def resultPointer : ExpHOL 64 := .rfield 0 (localVar "r")
def resultCount : ExpHOL 64 := .rfield 1 (localVar "r")
def loopTest : ExpHOL 64 := .cmp .less (localVar "i") resultCount
def lengthAddress : ExpHOL 64 := .op .add [resultPointer,.panop .mul [localVar "i",.const 16#64],.const 8#64]
def lengthExpression : ExpHOL 64 := .load .one lengthAddress
def lengthTest : ExpHOL 64 := .cmp .lower (localVar "maxb") lengthExpression
def lengthGuard : ProgHOL 64 := .ite lengthTest (.call (some (none,none)) (ofString "ssz_fail") [.const 70#64]) .skip
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def loopBody : ProgHOL 64 := .seq lengthGuard increment
def loop : ProgHOL 64 := .while loopTest loopBody
def returnArray : ProgHOL 64 := .return (localVar "r")
def initializedTail : ProgHOL 64 := .seq loop returnArray
def tail : ProgHOL 64 := .dec (ofString "i") .one (.const 0#64) initializedTail
def pairValue (array : BitVec 64) (count : Nat) : ValueHOL 64 := VarList.pairValue array count
def frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) := emptyLocalsHOLFinite {source with clock:=0}
def cell (array : BitVec 64) (index : Nat) : BitVec 64 := array+BitVec.ofNat 64 (16*index)+8#64

theorem body_shape : body=.decCall (ofString "r") VarList.returnShape (ofString "ssz_split_var_list") arguments tail := by
  simp only [body,Guest.Software.guestFn_decode_bytes_list,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    VarList.returnShape,arguments,tail,initializedTail,loop,loopTest,loopBody,lengthGuard,lengthTest,lengthExpression,lengthAddress,
    resultPointer,resultCount,increment,returnArray,localVar]

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.body_shape
