import Guest.SoftwareAst
import Guest.Model
import InitECandidate.Solver.Input.ScalarDeclaration
import InitECandidate.Solver.WitnessRadix.BindingLookup
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_udivmod with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",.one),(ofString "b",.one)]
def returnShape : ShapeHOL := .comb [.one,.one]
def zeroTest : ExpHOL 64 := .cmp .equal (localVar "b") (.const 0#64)
def zeroGuard : ProgHOL 64 := .ite zeroTest (.call (some (none,none)) (ofString "trap_with") [.const 2#64]) .skip
def smallTest : ExpHOL 64 := .cmp .lower (localVar "a") (localVar "b")
def smallGuard : ProgHOL 64 := .ite smallTest (.return (.rstruct [.const 0#64,localVar "a"])) .skip
def loopTest : ExpHOL 64 := .cmp .less (.const 0#64) (localVar "i")
def indexExpression : ExpHOL 64 := .op .sub [localVar "i",.const 1#64]
def remainderExpression : ExpHOL 64 := .op .or [
  .shift .lsl (localVar "r") (.const 1#64),
  .op .and [.shift .lsr (localVar "a") (localVar "i"),.const 1#64]]
def subtractTest : ExpHOL 64 := .cmp .notLower (localVar "r") (localVar "b")
def subtractExpression : ExpHOL 64 := .op .sub [localVar "r",localVar "b"]
def quotientExpression : ExpHOL 64 := .op .or [localVar "q",.shift .lsl (.const 1#64) (localVar "i")]
def subtractBody : ProgHOL 64 := .seq (.assign .local (ofString "r") subtractExpression) (.assign .local (ofString "q") quotientExpression)
def loopBody : ProgHOL 64 := .seq (.assign .local (ofString "i") indexExpression)
  (.seq (.assign .local (ofString "r") remainderExpression) (.ite subtractTest subtractBody .skip))
def loop : ProgHOL 64 := .while loopTest loopBody
def returnPair : ProgHOL 64 := .return (.rstruct [localVar "q",localVar "r"])
def initializedBody : ProgHOL 64 := .seq loop returnPair
def setupProgram : ProgHOL 64 := .dec (ofString "q") .one (.const 0#64)
  (.dec (ofString "r") .one (.const 0#64) (.dec (ofString "i") .one (.const 64#64) initializedBody))

theorem body_shape : body=.seq zeroGuard (.seq smallGuard setupProgram) := by
  simp only [body,Guest.Software.guestFn_udivmod,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    zeroGuard,zeroTest,smallGuard,smallTest,setupProgram,initializedBody,loop,loopTest,loopBody,indexExpression,
    remainderExpression,subtractTest,subtractBody,subtractExpression,quotientExpression,returnPair,localVar]

def shifted (a r : BitVec 64) (index : Nat) : BitVec 64 := (r<<<(1:Nat)) ||| ((a>>>(index-1)) &&& 1#64)
def takeSubtract (a b r : BitVec 64) (index : Nat) : Prop := b.toNat≤(shifted a r index).toNat
instance (a b r : BitVec 64) (index : Nat) : Decidable (takeSubtract a b r index) := inferInstanceAs (Decidable (_≤_))
def nextQ (a b q r : BitVec 64) (index : Nat) : BitVec 64 := if takeSubtract a b r index then q ||| (1#64<<<(index-1)) else q
def nextR (a b r : BitVec 64) (index : Nat) : BitVec 64 := if takeSubtract a b r index then shifted a r index-b else shifted a r index
def step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b q r : BitVec 64) (index : Nat) :=
  let first:=bind (bind source "i" (BitVec.ofNat 64 (index-1))) "r" (shifted a r index)
  if takeSubtract a b r index then bind (bind first "r" (shifted a r index-b)) "q" (q ||| (1#64<<<(index-1))) else first

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.body_shape
