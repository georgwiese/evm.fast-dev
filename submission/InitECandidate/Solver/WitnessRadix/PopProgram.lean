import InitECandidate.Solver.WitnessRadix.TerminalProgram
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.WitnessRadix.PopProgram
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open QueryBranch

def pendingExpression (name : String) : ExpHOL 64 :=
  .load .one (.op .add [localVar name, .panop .mul [localVar "depth", .const 8#64]])
def decrement : ProgHOL 64 :=
  .assign .local (ofString "depth") (.op .sub [localVar "depth", .const 1#64])
def startAssignment : ProgHOL 64 :=
  .assign .local (ofString "start") (pendingExpression "pending_start")
def countAssignment : ProgHOL 64 :=
  .assign .local (ofString "count") (pendingExpression "pending_count")
def bitExpression : ExpHOL 64 := addConst (.load .one (localVar "parent")) 1#64
def destExpression : ExpHOL 64 := addConst (localVar "parent") 16#64
def bitAssignment : ProgHOL 64 := .assign .local (ofString "bit") bitExpression
def destAssignment : ProgHOL 64 := .assign .local (ofString "dest") destExpression
def afterParent : ProgHOL 64 := .seq bitAssignment (.seq destAssignment .continue)

theorem pop_shape : TerminalProgram.popCode =
    .seq decrement (.seq startAssignment (.seq countAssignment
      (.dec (ofString "parent") .one (pendingExpression "pending_node") afterParent))) := by
  simp only [TerminalProgram.popCode, TerminalProgram.afterStore, TerminalProgram.terminalCode,
    BuildEntry.mainBody, BuildEntry.mainLoop, BuildProgram.loops, BuildProgram.body,
    RawProgram.guestFn_solver_radix_index, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some, decrement, startAssignment, countAssignment,
    pendingExpression, afterParent, bitAssignment, destAssignment, bitExpression, destExpression,
    localVar, addConst]

end InitECandidate.Solver.WitnessRadix.PopProgram

#print axioms InitECandidate.Solver.WitnessRadix.PopProgram.pop_shape
