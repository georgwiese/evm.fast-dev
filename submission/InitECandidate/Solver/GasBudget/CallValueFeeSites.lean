import InitECandidate.Solver.GasBudget.CallValueFee
import InitECandidate.Solver.GasBudget.ForwardSites

namespace InitECandidate.Solver.GasBudget.CallValueFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def sites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.decCall name _ function _ rest) =>
      (if name = ofString "need" ∧ function = ofString "add_sat" then [code] else []) ++ sites rest
  | .seq first second | .ite _ first second => sites first ++ sites second
  | .dec _ _ _ rest | .while _ rest => sites rest
  | _ => []
def eraseContinuation : ProgHOL 64 → ProgHOL 64
  | .decCall name shape function arguments (.seq charge _) => .decCall name shape function arguments (.seq charge .skip)
  | _ => .skip
def selected (declaration : Decl (BitVec 64)) : ProgHOL 64 :=
  match declaration with
  | .function fn => eraseContinuation (((sites (progToHOL fn.body))[0]?).getD .skip)
  | _ => .skip

set_option maxRecDepth 10000 in
/-- The checked need/charge sequence is literal unchanged CALL/CALLCODE
syntax. The warmth lookup and value-zero test still precede this site. -/
theorem opcode_sites : selected Guest.guestFn_op_call = program .skip ∧ selected Guest.guestFn_op_callcode = program .skip := by
  constructor
  all_goals simp only [selected, Guest.guestFn_op_call, Guest.guestFn_op_callcode, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, sites, ↓reduceIte,
    List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some, eraseContinuation]
  all_goals rfl

end InitECandidate.Solver.GasBudget.CallValueFee

#print axioms InitECandidate.Solver.GasBudget.CallValueFee.opcode_sites
