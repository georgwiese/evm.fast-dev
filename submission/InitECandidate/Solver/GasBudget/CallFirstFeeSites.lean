import InitECandidate.Solver.GasBudget.CallFirstFee

namespace InitECandidate.Solver.GasBudget.CallFirstFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def warmSites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.decCall _ _ function _ rest) =>
      (if function = ofString "is_warm_address" then [code] else []) ++ warmSites rest
  | .seq first second | .ite _ first second => warmSites first ++ warmSites second
  | .dec _ _ _ rest | .while _ rest => warmSites rest
  | _ => []
def cutCharge : ProgHOL 64 → ProgHOL 64
  | .seq call@(.call (some (none, none)) function arguments) rest =>
      if function = ofString "charge_gas" then .seq call .skip else .seq (.call (some (none, none)) function arguments) (cutCharge rest)
  | .seq first second => .seq (cutCharge first) (cutCharge second)
  | .ite test yes no => .ite test (cutCharge yes) (cutCharge no)
  | .dec name shape expression rest => .dec name shape expression (cutCharge rest)
  | .decCall name shape function arguments rest => .decCall name shape function arguments (cutCharge rest)
  | .while test rest => .while test (cutCharge rest)
  | other => other
def selected : ProgHOL 64 := match Guest.guestFn_op_call with
  | .function fn => cutCharge (((warmSites (progToHOL fn.body))[0]?).getD .skip)
  | _ => .skip

set_option maxRecDepth 10000 in
/-- The checked warmth/access/value/add/charge prefix is literal original
CALL syntax; only the continuation after the first charge is discarded. -/
theorem original_site : selected = program [localVar "to"] .skip := by
  simp only [selected, Guest.guestFn_op_call, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, Option.map_some, warmSites, ↓reduceIte, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some, cutCharge]
  rfl

theorem price_exact (count : Nat) : Has.bodyPrice .account count + 4 = 8 * count + 6 := by
  change (20 / 8 + 20 % 8 + 2) * count + (1 + 1) + 4 = 8 * count + 6
  omega

end InitECandidate.Solver.GasBudget.CallFirstFee

#print axioms InitECandidate.Solver.GasBudget.CallFirstFee.original_site
#print axioms InitECandidate.Solver.GasBudget.CallFirstFee.price_exact
