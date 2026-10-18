import InitECandidate.Solver.MutableTable.DeleteModelBudget
import InitECandidate.Solver.ClockStutter
import InitECandidate.Solver.MutableTable.ReadCallEnvironment

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htab_truncate with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := ReadCall.formals "n"
def condition : ExpHOL 64 := .cmp .lower (localVar "n") (Find.tableLoad 24#64)
def lastPosition : ExpHOL 64 := .op .sub [Find.tableLoad 24#64, .const 1#64]
def orderRead : ExpHOL 64 := .load .one (.op .add [Find.tableLoad 56#64, .panop .mul [localVar "pos", .const 8#64]])
def keyAddress : ExpHOL 64 := .op .add [Find.tableLoad 32#64, .panop .mul [localVar "slot", localVar "stride"]]
def deleteCall : ProgHOL 64 := .call (some (none, none)) (ofString "htab_del") [localVar "t", keyAddress]
def loopBody : ProgHOL 64 := .dec (ofString "pos") .one lastPosition (.dec (ofString "slot") .one orderRead deleteCall)
def loop : ProgHOL 64 := .while condition loopBody
def returnZero : ProgHOL 64 := .return (.const 0#64)
def tail : ProgHOL 64 := .seq loop returnZero

theorem body_shape : body = .dec (ofString "stride") .one (Find.tableLoad 8#64) tail := by
  simp only [body, Guest.guestFn_htab_truncate, progToHOL, expToHOL, shapeToHOL, Find.tableLoad, localVar, tail,
    loop, condition, loopBody, lastPosition, orderRead, deleteCall, keyAddress, returnZero, List.map_cons, List.map_nil, Option.map_none]

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.body_shape
