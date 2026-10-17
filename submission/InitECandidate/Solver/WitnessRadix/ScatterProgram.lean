import InitECandidate.Solver.WitnessRadix.CountProgram

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open QueryBranch BuildProgram

def body : ProgHOL 64 := (loops BuildProgram.body)[2]?.map (fun loop =>
  match loop with | .while _ code => code | _ => .skip) |>.getD .skip
def cursorAddress (cursor : String) : ExpHOL 64 :=
  .op .add [localVar "dst", .panop .mul [localVar cursor, .const 8#64]]
def increaseCursor (cursor : String) : ProgHOL 64 :=
  .assign .local (ofString cursor) (addConst (localVar cursor) 1#64)
def writeBucket (cursor : String) : ProgHOL 64 :=
  .seq (.store (cursorAddress cursor) (localVar "ordinal")) (increaseCursor cursor)
def afterDigit : ProgHOL 64 :=
  .seq (.ite CountProgram.digitTest (writeBucket "zero_cursor") (writeBucket "one_cursor")) increment

theorem body_shape : body =
    .dec (ofString "ordinal") .one CountProgram.ordinalExpression
      (.dec (ofString "digit") .one CountProgram.digitExpression afterDigit) := by
  simp only [body, loops, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some,
    CountProgram.ordinalExpression, CountProgram.digitExpression, CountProgram.digitTest,
    afterDigit, writeBucket, increaseCursor, cursorAddress, increment, arrayAddress,
    addConst, localVar]

theorem loop_shape : (loops BuildProgram.body)[2]? = some (.while condition body) := by
  simp only [body, loops, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some,
    condition, localVar]

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.body_shape
#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.loop_shape
