import InitECandidate.Solver.Input.CurrentVerify.RunAttempt
import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterPayload : ProgHOL 64 := match body with | .dec _ _ _ rest=>rest | _=>.skip
def headerCall : ProgHOL 64 := match afterPayload with | .seq _ rest=>rest | _=>.skip
def afterHeaders : ProgHOL 64 := match headerCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def field (offset : Nat) : ExpHOL 64 := .load .one (.op .add [localVar "si",.const (BitVec.ofNat 64 offset)])
def headerArguments : List (ExpHOL 64) := [field 72,field 80]
def headerShape : ShapeHOL := .comb [.one,.one]

set_option maxRecDepth 100000 in
/-- The actual current first validator call, without an old gas-check-free
run_attempt body or obsolete validator/crypto contract. -/
theorem header_shapes :
    body=.dec (ofString "pl") .one (field 0) afterPayload ∧
    afterPayload=.seq .skip headerCall ∧
    headerCall=.decCall (ofString "vh") headerShape (ofString "validate_headers") headerArguments afterHeaders := by
  simp only [body,afterPayload,headerCall,afterHeaders,field,headerArguments,headerShape,localVar,
    Guest.Software.guestFn_run_attempt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  trivial

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.header_shapes
