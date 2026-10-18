import InitECandidate.Solver.GasBudget.FrameField
import InitECandidate.Solver.GasBudget.HaltNormal
import InitECandidate.Solver.GasBudget.RefundNormal

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_frame_exception with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "err", .one)]
def refill : ProgHOL 64 := .call (some (none, none)) (ofString "refill_frame_state_gas") []
def halt : ProgHOL 64 := .call (some (none, none)) (ofString "frame_halt") [localVar "err"]
def returnZero : ProgHOL 64 := .return (.const 0#64)
def condition : ExpHOL 64 := .cmp .notEqual (localVar "err") (.const 1#64)
def clearData : ProgHOL 64 := .seq (.store (frameAddress 120#64) (.var .global (ofString "evm_empty")))
  (.store (frameAddress 128#64) (.const 0#64))
def regularError : ProgHOL 64 := .seq halt clearData
def specialError : ProgHOL 64 := .store (frameAddress 160#64) (localVar "err")
def choice : ProgHOL 64 := .ite condition regularError specialError
def doneAddress : ExpHOL 64 := addConst (.var .global (ofString "cur_cont")) 32#64
def markDone : ProgHOL 64 := .store doneAddress (.const 1#64)

theorem body_shape : body = .seq refill (.seq choice (.seq markDone returnZero)) := by
  simp only [body, Guest.guestFn_frame_exception, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, refill, choice, condition, regularError, specialError, halt, clearData,
    markDone, doneAddress, returnZero, frameAddress, localVar, addConst]

theorem choice_safe : Input.LocalPrefix (ofString "err") choice := by
  exact .ite _ (.seq (.call none _ _ (by intro name impossible; cases impossible)) (.seq (.store _ _) (.store _ _))) (.store _ _)

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.body_shape
#print axioms InitECandidate.Solver.GasBudget.FrameException.choice_safe
