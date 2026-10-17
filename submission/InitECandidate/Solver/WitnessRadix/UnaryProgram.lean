import InitECandidate.Solver.WitnessRadix.TerminalProgram
import InitECandidate.Solver.WitnessRadix.CountLoop

namespace InitECandidate.Solver.WitnessRadix.UnaryProgram
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open QueryBranch

def afterCount : ProgHOL 64 := match TerminalProgram.remainingCode with
  | .dec _ _ _ (.dec _ _ _ (.seq _ code)) => code | _ => .skip
def splitCode : ProgHOL 64 := match afterCount with | .seq _ code => code | _ => .skip
def unaryTest : ExpHOL 64 :=
  .cmp .notEqual (.const 0#64) (.op .or [
    .cmp .equal (localVar "zeros") (.const 0#64),
    .cmp .equal (localVar "zeros") (localVar "count")])
def bitAssignment : ProgHOL 64 :=
  .assign .local (ofString "bit") (addConst (localVar "bit") 1#64)
def unaryBody : ProgHOL 64 := .seq bitAssignment .continue

theorem remaining_shape : TerminalProgram.remainingCode =
    .dec (ofString "zeros") .one (.const 0#64)
      (.dec (ofString "i") .one (.const 0#64) (.seq CountProgram.countLoop afterCount)) := by
  simp only [TerminalProgram.remainingCode, afterCount, BuildEntry.mainBody, BuildEntry.mainLoop,
    BuildProgram.loops, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Option.map_some, CountProgram.countLoop, CountProgram.body,
    BuildProgram.condition, localVar]

theorem after_count_shape : afterCount = .seq (.ite unaryTest unaryBody .skip) splitCode := by
  simp only [afterCount, splitCode, TerminalProgram.remainingCode, BuildEntry.mainBody, BuildEntry.mainLoop,
    BuildProgram.loops, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    unaryTest, unaryBody, bitAssignment, localVar, addConst]

end InitECandidate.Solver.WitnessRadix.UnaryProgram

#print axioms InitECandidate.Solver.WitnessRadix.UnaryProgram.remaining_shape
#print axioms InitECandidate.Solver.WitnessRadix.UnaryProgram.after_count_shape
