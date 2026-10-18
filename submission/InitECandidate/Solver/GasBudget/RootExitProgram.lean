import InitECandidate.Solver.GasBudget.FrameEpilogueCall
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.GlobalAssignNormal
import InitECandidate.Solver.GasBudget.FrameTableFloor

namespace InitECandidate.Solver.GasBudget.RootExit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def runBody : ProgHOL 64 := match Guest.guestFn_run_frames with | .function fn => progToHOL fn.body | _ => .skip
def selected : ProgHOL 64 := match runBody with
  | .dec _ _ _ (.seq (.while _ (.dec _ _ _ (.seq _ (.ite _ branch _)))) _) => branch
  | _ => .skip
def childBranch : ProgHOL 64 := match selected with | .seq _ (.seq _ (.ite _ _ branch)) => branch | _ => .skip
def recordLoad (offset : BitVec 64) : ExpHOL 64 := .load .one (addConst (.var .global (ofString "cur_cont")) offset)
def condition : ExpHOL 64 := .cmp .equal (recordLoad 16#64) (.const 0#64)
def setParent : ProgHOL 64 := .assign .global (ofString "ev") (recordLoad 0#64)
def setContinuation : ProgHOL 64 := .assign .global (ofString "cur_cont") (recordLoad 8#64)
def setGo : ProgHOL 64 := .assign .local (ofString "go") (.const 0#64)
def rootBranch : ProgHOL 64 := .seq setParent (.seq setContinuation setGo)
def epilogue : ProgHOL 64 := .call (some (none, none)) (ofString "frame_epilogue") []

theorem actual_site : selected = .seq .skip (.seq epilogue (.ite condition rootBranch childBranch)) := by
  simp only [selected, runBody, Guest.guestFn_run_frames, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, childBranch, epilogue, condition, recordLoad,
    rootBranch, setParent, setContinuation, setGo, addConst]

end InitECandidate.Solver.GasBudget.RootExit

#print axioms InitECandidate.Solver.GasBudget.RootExit.actual_site
