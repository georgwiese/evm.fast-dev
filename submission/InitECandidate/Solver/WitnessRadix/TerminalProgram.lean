import InitECandidate.Solver.WitnessRadix.BuildEntry

namespace InitECandidate.Solver.WitnessRadix.TerminalProgram
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open QueryBranch

def terminalCode : ProgHOL 64 := match BuildEntry.mainBody with
  | .seq (.ite _ code _) _ => code | _ => .skip
def remainingCode : ProgHOL 64 := match BuildEntry.mainBody with
  | .seq _ code => code | _ => .skip
def afterStore : ProgHOL 64 := match terminalCode with
  | .dec _ _ _ (.seq _ code) => code | _ => .skip
def popCode : ProgHOL 64 := match afterStore with | .seq _ code => code | _ => .skip
def terminalTest : ExpHOL 64 :=
  .cmp .notEqual (.const 0#64) (.op .or [
    .cmp .equal (localVar "count") (.const 1#64),
    .cmp .equal (localVar "bit") (.const 256#64)])
def depthTest : ExpHOL 64 := .cmp .equal (localVar "depth") (.const 0#64)
def ordinalExpression : ExpHOL 64 :=
  .load .one (.op .add [localVar "src", .panop .mul [
    .op .sub [.op .add [localVar "start", localVar "count"], .const 1#64], .const 8#64]])
def tagExpression : ExpHOL 64 :=
  .op .add [.panop .mul [localVar "ordinal", .const 2#64], .const 1#64]

theorem main_loop_shape : BuildEntry.mainLoop = .while (.const 1#64) BuildEntry.mainBody := by
  simp only [BuildEntry.mainBody, BuildEntry.mainLoop, BuildProgram.loops, BuildProgram.body,
    RawProgram.guestFn_solver_radix_index, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some]

theorem main_body_shape : BuildEntry.mainBody =
    .seq (.ite terminalTest terminalCode .skip) remainingCode := by
  simp only [terminalCode, remainingCode, BuildEntry.mainBody, BuildEntry.mainLoop,
    BuildProgram.loops, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    terminalTest, localVar]

theorem terminal_shape : terminalCode = .dec (ofString "ordinal") .one ordinalExpression
    (.seq (.store (localVar "dest") tagExpression) afterStore) := by
  simp only [terminalCode, afterStore, BuildEntry.mainBody, BuildEntry.mainLoop,
    BuildProgram.loops, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    ordinalExpression, tagExpression, localVar]

theorem after_store_shape : afterStore =
    .seq (.ite depthTest BuildEntry.returnZero .skip) popCode := by
  simp only [afterStore, popCode, terminalCode, BuildEntry.mainBody, BuildEntry.mainLoop,
    BuildProgram.loops, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    depthTest, BuildEntry.returnZero, localVar]

end InitECandidate.Solver.WitnessRadix.TerminalProgram

#print axioms InitECandidate.Solver.WitnessRadix.TerminalProgram.terminal_shape
#print axioms InitECandidate.Solver.WitnessRadix.TerminalProgram.after_store_shape
