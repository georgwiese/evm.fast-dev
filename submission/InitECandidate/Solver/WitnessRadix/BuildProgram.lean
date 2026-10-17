import InitECandidate.Solver.WitnessRadix.QueryBranch

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.WitnessRadix.BuildProgram
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open QueryBranch

def body : ProgHOL 64 :=
  match RawProgram.guestFn_solver_radix_index with
  | .function fn => progToHOL fn.body
  | _ => .skip

def loops : ProgHOL 64 → List (ProgHOL 64)
  | .while condition body => .while condition body :: loops body
  | .dec _ _ _ body | .decCall _ _ _ _ body => loops body
  | .seq left right | .ite _ left right => loops left ++ loops right
  | _ => []

def copyBody : ProgHOL 64 := (loops body)[3]?.map (fun loop =>
  match loop with | .while _ code => code | _ => .skip) |>.getD .skip

def arrayAddress (base : String) : ExpHOL 64 :=
  .op .add [localVar base, .panop .mul [
    .op .add [localVar "start", localVar "i"], .const 8#64]]
def increment : ProgHOL 64 :=
  .assign .local (ofString "i") (addConst (localVar "i") 1#64)
def condition : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "count")

theorem copy_body_shape : copyBody =
    .seq (.store (arrayAddress "src") (.load .one (arrayAddress "dst"))) increment := by
  simp only [copyBody, loops, body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some,
    arrayAddress, increment, localVar, addConst]

theorem copy_loop_shape : (loops body)[3]? = some (.while condition copyBody) := by
  simp only [copyBody, loops, body, RawProgram.guestFn_solver_radix_index,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some,
    condition, localVar]

end InitECandidate.Solver.WitnessRadix.BuildProgram

#print axioms InitECandidate.Solver.WitnessRadix.BuildProgram.copy_body_shape
#print axioms InitECandidate.Solver.WitnessRadix.BuildProgram.copy_loop_shape
