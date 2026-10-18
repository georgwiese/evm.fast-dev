import InitECandidate.Solver.GasBudget.RootExitNormal
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def condition : ExpHOL 64 := .cmp .notEqual (localVar "go") (.const 0#64)
def doneCondition : ExpHOL 64 := .cmp .notEqual (localVar "done") (.const 0#64)
def loopBody : ProgHOL 64 := match RootExit.runBody with | .dec _ _ _ (.seq (.while _ body) _) => body | _ => .skip
def head : ProgHOL 64 := match loopBody with | .dec _ _ _ (.seq head _) => head | _ => .skip
def dispatchBranch : ProgHOL 64 := match head with | .ite _ _ branch => branch | _ => .skip
def markedCondition : ExpHOL 64 := .cmp .notEqual (RootExit.recordLoad 32#64) (.const 0#64)
def markDone : ProgHOL 64 := .assign .local (ofString "done") (.const 1#64)
def haltedCondition : ExpHOL 64 := .cmp .equal (frameLoad 104#64) (.const 0#64)
def pcBranch : ProgHOL 64 := match dispatchBranch with | .ite _ _ branch => branch | _ => .skip
def codeEndCondition : ExpHOL 64 := .cmp .notLower (localVar "pc") (frameLoad 56#64)
def opcodeBranch : ProgHOL 64 := match pcBranch with | .dec _ _ _ (.ite _ _ branch) => branch | _ => .skip
def loop : ProgHOL 64 := .while condition loopBody

theorem body_shape : RootExit.runBody = .dec (ofString "go") .one (.const 1#64) (.seq loop (.return (.const 0#64))) := by
  simp only [RootExit.runBody, Guest.guestFn_run_frames, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, loop, condition, loopBody, localVar]

theorem loop_body_shape : loopBody = .dec (ofString "done") .one (.const 0#64)
    (.seq head (.ite doneCondition RootExit.selected .skip)) := by
  simp only [loopBody, RootExit.runBody, Guest.guestFn_run_frames, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, head, doneCondition, RootExit.selected, localVar]

theorem head_shape : head = .ite markedCondition markDone dispatchBranch := by
  simp only [head, loopBody, RootExit.runBody, Guest.guestFn_run_frames, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, markedCondition, markDone, dispatchBranch, RootExit.recordLoad, addConst]

theorem dispatch_shape : dispatchBranch = .ite haltedCondition markDone pcBranch := by
  simp only [dispatchBranch, head, loopBody, RootExit.runBody, Guest.guestFn_run_frames, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, haltedCondition, markDone, pcBranch, frameLoad, frameAddress]

theorem pc_shape : pcBranch = .dec (ofString "pc") .one (frameLoad 0#64) (.ite codeEndCondition markDone opcodeBranch) := by
  simp only [pcBranch, dispatchBranch, head, loopBody, RootExit.runBody, Guest.guestFn_run_frames, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, codeEndCondition, markDone, opcodeBranch, frameLoad, frameAddress, localVar]

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.body_shape
#print axioms InitECandidate.Solver.GasBudget.RunFrames.loop_body_shape
#print axioms InitECandidate.Solver.GasBudget.RunFrames.head_shape
#print axioms InitECandidate.Solver.GasBudget.RunFrames.dispatch_shape
#print axioms InitECandidate.Solver.GasBudget.RunFrames.pc_shape
