import InitECandidate.Solver.GasBudget.FrameOpenNormalCall
import InitECandidate.Solver.Input.PureGuard
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.GasBudget.ProcessMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_process_message with | .function fn => progToHOL fn.body | _ => .skip
def depthGuard : ProgHOL 64 := .ite (.cmp .lower (.const 1024#64) (.load .one (addConst (localVar "msg") 128#64)))
  (.raise (ofString "EvmErr") (.const 7#64)) .skip
def afterOpen : ProgHOL 64 := match body with
  | .seq _ (.seq .skip (.dec _ _ _ (.dec _ _ _ (.decCall _ _ _ _ rest)))) => rest | _ => .skip
def openSite : ProgHOL 64 := .decCall (ofString "child") .one (ofString "frame_open") [localVar "msg", .const 0#64] afterOpen
def parentScopes : ProgHOL 64 := .dec (ofString "parent") .one (.var .global (ofString "ev"))
  (.dec (ofString "parent_cont") .one (.var .global (ofString "cur_cont")) openSite)

theorem body_shape : body = .seq depthGuard (.seq .skip parentScopes) := by
  simp only [body, afterOpen, Guest.guestFn_process_message, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, depthGuard, parentScopes, openSite, addConst, localVar]

theorem guard_read_only : Input.PureGuard depthGuard := .ite _ (.raise _ _) .skip

end InitECandidate.Solver.GasBudget.ProcessMessage

#print axioms InitECandidate.Solver.GasBudget.ProcessMessage.body_shape
#print axioms InitECandidate.Solver.GasBudget.ProcessMessage.guard_read_only
