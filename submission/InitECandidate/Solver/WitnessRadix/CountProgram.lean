import InitECandidate.Solver.WitnessRadix.BuildProgram
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.WitnessRadix.CountProgram
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open QueryBranch BuildProgram

def body : ProgHOL 64 := (loops BuildProgram.body)[1]?.map (fun loop =>
  match loop with | .while _ code => code | _ => .skip) |>.getD .skip
def ordinalExpression : ExpHOL 64 := .load .one (arrayAddress "src")
def digitExpression : ExpHOL 64 :=
  .op .and [
    .shift .lsr (.loadByte (.op .add [localVar "keys",
      .panop .mul [localVar "ordinal", .const 32#64],
      .shift .lsr (localVar "bit") (.const 3#64)]))
      (.op .and [localVar "bit", .const 7#64]), .const 1#64]
def digitTest : ExpHOL 64 := .cmp .equal (localVar "digit") (.const 0#64)
def increaseZeros : ProgHOL 64 :=
  .assign .local (ofString "zeros") (addConst (localVar "zeros") 1#64)
def afterDigit : ProgHOL 64 :=
  .seq (.ite digitTest increaseZeros .skip) increment

theorem body_shape : body =
    .dec (ofString "ordinal") .one ordinalExpression
      (.dec (ofString "digit") .one digitExpression afterDigit) := by
  simp only [body, loops, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some,
    ordinalExpression, digitExpression, afterDigit, digitTest, increaseZeros,
    increment, arrayAddress, addConst, localVar]

theorem loop_shape : (loops BuildProgram.body)[1]? = some (.while condition body) := by
  simp only [body, loops, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some,
    condition, localVar]

end InitECandidate.Solver.WitnessRadix.CountProgram

#print axioms InitECandidate.Solver.WitnessRadix.CountProgram.body_shape
#print axioms InitECandidate.Solver.WitnessRadix.CountProgram.loop_shape
