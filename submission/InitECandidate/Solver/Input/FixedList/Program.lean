import InitECandidate.Solver.Input.UDivMod.Call
import InitECandidate.Solver.Input.GuardNormal

namespace InitECandidate.Solver.Input.FixedList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_ssz_fixed_list_count with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "len",.one),(ofString "sz",.one),(ofString "lim",.one)]
def arguments : List (ExpHOL 64) := [localVar "len",localVar "sz"]
def quotient : ExpHOL 64 := .rfield 0 (localVar "qr")
def remainder : ExpHOL 64 := .rfield 1 (localVar "qr")
def remainderTest : ExpHOL 64 := .cmp .notEqual remainder (.const 0#64)
def limitTest : ExpHOL 64 := .cmp .lower (localVar "lim") quotient
def returnCount : ProgHOL 64 := .return quotient
def limitTail : ProgHOL 64 := .seq (.ite limitTest (.call (some (none,none)) (ofString "ssz_fail") [.const 31#64]) .skip) returnCount
def tail : ProgHOL 64 := .seq (.ite remainderTest (.call (some (none,none)) (ofString "ssz_fail") [.const 30#64]) .skip) limitTail

theorem body_shape : body=.decCall (ofString "qr") UDivMod.returnShape (ofString "udivmod") arguments tail := by
  simp only [body,Guest.guestFn_ssz_fixed_list_count,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    arguments,tail,remainderTest,remainder,limitTail,limitTest,quotient,returnCount,UDivMod.returnShape,localVar]

end InitECandidate.Solver.Input.FixedList

#print axioms InitECandidate.Solver.Input.FixedList.body_shape
