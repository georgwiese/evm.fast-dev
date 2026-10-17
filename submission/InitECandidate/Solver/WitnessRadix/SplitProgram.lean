import InitECandidate.Solver.WitnessRadix.UnaryProgram
import InitECandidate.Solver.WitnessRadix.ScatterLoop
import InitECandidate.Solver.WitnessRadix.BuildCopyLoop

namespace InitECandidate.Solver.WitnessRadix.SplitProgram
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open QueryBranch

def allocationCode : ProgHOL 64 := match UnaryProgram.splitCode with
  | .dec _ _ _ (.dec _ _ _ (.seq _ (.seq _ (.seq _ (.seq _ code))))) => code
  | _ => .skip
def resetIndex : ProgHOL 64 := .assign .local (ofString "i") (.const 0#64)
def assign (name : String) (expression : ExpHOL 64) : ProgHOL 64 :=
  .assign .local (ofString name) expression
def pendingAddress (name : String) : ExpHOL 64 :=
  .op .add [localVar name, .panop .mul [localVar "depth", .const 8#64]]

def allocationOps : List (ProgHOL 64) :=
  [assign "node_next" (addConst (localVar "node_next") 24#64),
   .store (localVar "node") (localVar "bit"),
   .store (addConst (localVar "node") 8#64) (.const 0#64),
   .store (addConst (localVar "node") 16#64) (.const 0#64),
   .store (localVar "dest") (localVar "node"),
   .store (pendingAddress "pending_start") (.op .add [localVar "start", localVar "zeros"]),
   .store (pendingAddress "pending_count") (.op .sub [localVar "count", localVar "zeros"]),
   .store (pendingAddress "pending_node") (localVar "node"),
   assign "depth" (addConst (localVar "depth") 1#64),
   assign "count" (localVar "zeros"),
   assign "dest" (addConst (localVar "node") 8#64),
   assign "bit" (addConst (localVar "bit") 1#64)]

def sequence : List (ProgHOL 64) → ProgHOL 64
  | [] => .skip
  | first :: rest => match rest with
    | [] => first
    | second :: tail => .seq first (sequence (second :: tail))
def allocationBody : ProgHOL 64 := sequence allocationOps

theorem split_shape : UnaryProgram.splitCode =
    .dec (ofString "zero_cursor") .one (localVar "start")
      (.dec (ofString "one_cursor") .one (.op .add [localVar "start", localVar "zeros"])
        (.seq resetIndex (.seq ScatterProgram.scatterLoop (.seq resetIndex
          (.seq BuildCopy.copyLoop allocationCode))))) := by
  simp only [UnaryProgram.splitCode, UnaryProgram.afterCount, TerminalProgram.remainingCode,
    BuildEntry.mainBody, BuildEntry.mainLoop, BuildProgram.loops, BuildProgram.body,
    RawProgram.guestFn_solver_radix_index, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some,
    allocationCode, resetIndex, localVar, ScatterProgram.scatterLoop, ScatterProgram.body,
    BuildCopy.copyLoop, BuildProgram.copyBody, BuildProgram.condition]

theorem allocation_shape : allocationCode =
    .dec (ofString "node") .one (localVar "node_next") allocationBody := by
  simp only [allocationCode, allocationBody, allocationOps, sequence, assign, pendingAddress,
    UnaryProgram.splitCode, UnaryProgram.afterCount, TerminalProgram.remainingCode,
    BuildEntry.mainBody, BuildEntry.mainLoop, BuildProgram.loops, BuildProgram.body,
    RawProgram.guestFn_solver_radix_index, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some, localVar, addConst]

end InitECandidate.Solver.WitnessRadix.SplitProgram

#print axioms InitECandidate.Solver.WitnessRadix.SplitProgram.split_shape
#print axioms InitECandidate.Solver.WitnessRadix.SplitProgram.allocation_shape
