import InitECandidate.Solver.Input.WhileActive
import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.Input.RlpLength.Be
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_be_len with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "v",.one)]
def loopTest : ExpHOL 64 := .cmp .notEqual (localVar "v") (.const 0#64)
def shiftExpression : ExpHOL 64 := .shift .lsr (localVar "v") (.const 8#64)
def incrementExpression : ExpHOL 64 := .op .add [localVar "n",.const 1#64]
def loopBody : ProgHOL 64 := .seq (.assign .local (ofString "v") shiftExpression) (.assign .local (ofString "n") incrementExpression)
def loop : ProgHOL 64 := .while loopTest loopBody
def returnCount : ProgHOL 64 := .return (localVar "n")
def initializedTail : ProgHOL 64 := .seq loop returnCount
def step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (count : Nat) :=
  bind (bind source "v" (value>>>(8:Nat))) "n" (BitVec.ofNat 64 (count+1))

theorem body_shape : body=.dec (ofString "n") .one (.const 0#64) initializedTail := by
  simp only [body,Guest.guestFn_rlp_be_len,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    initializedTail,loop,loopTest,loopBody,shiftExpression,incrementExpression,returnCount,localVar]

end InitECandidate.Solver.Input.RlpLength.Be

#print axioms InitECandidate.Solver.Input.RlpLength.Be.body_shape
