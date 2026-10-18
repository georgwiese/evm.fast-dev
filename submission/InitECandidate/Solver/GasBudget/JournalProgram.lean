import InitECandidate.Solver.Input.GlobalAssign
import InitECandidate.Solver.Input.LoopNormal
import Guest.Ast

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def countVar : ExpHOL 64 := .var .global (ofString "journal_n")
def journalVar : ExpHOL 64 := .var .global (ofString "journal")
def condition : ExpHOL 64 := .cmp .lower (localVar "snap") countVar
def decrement : ProgHOL 64 := .assign .global (ofString "journal_n") (.op .sub [countVar, .const 1#64])
def recordExpression : ExpHOL 64 := .op .add [journalVar, .panop .mul [countVar, .const 32#64]]
def recordField (offset : BitVec 64) : ExpHOL 64 := .load .one (.op .add [localVar "r", .const offset])
def setCall : ProgHOL 64 := .call (some (none, none)) (ofString "htab_set") [localVar "t", localVar "key", recordField 24#64]
def deleteCall : ProgHOL 64 := .call (some (none, none)) (ofString "htab_del") [localVar "t", localVar "key"]
def selectCall : ProgHOL 64 := .ite (.cmp .notEqual (recordField 16#64) (.const 0#64)) setCall deleteCall
def records : ProgHOL 64 := .dec (ofString "r") .one recordExpression
  (.dec (ofString "t") .one (.load .one (localVar "r"))
    (.dec (ofString "key") .one (recordField 8#64) selectCall))
def loopBody : ProgHOL 64 := .seq decrement records
def loop : ProgHOL 64 := .while condition loopBody
def body : ProgHOL 64 := match Guest.guestFn_state_restore with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "snap", .one)]

theorem body_shape : body = .seq loop (.return (.const 0#64)) := by
  simp only [body, Guest.guestFn_state_restore, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, loop, condition, loopBody,
    decrement, records, recordExpression, recordField, selectCall, setCall, deleteCall, countVar, journalVar, localVar]

theorem body_safe : Input.LocalPrefix (ofString "snap") loopBody :=
  .seq (.globalAssign _ _) (.dec _ _ _ (by decide) (.dec _ _ _ (by decide)
    (.dec _ _ _ (by decide) (.ite _ (.call none _ _ (by intro name impossible; cases impossible))
      (.call none _ _ (by intro name impossible; cases impossible))))))

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.body_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.body_safe
