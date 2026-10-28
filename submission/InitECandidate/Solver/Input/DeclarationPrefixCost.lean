import InitECandidate.Solver.Input.ClockCost

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang

/-- Remove at most n leading local declarations, retaining their literal tail. -/
def dropDeclarations : Nat → ProgHOL 64 → ProgHOL 64
  | 0,program=>program
  | n+1,.dec _ _ _ rest=>dropDeclarations n rest
  | _+1,program=>program

/-- Declaration reads, shape failures and local restoration spend no source
clock; a uniform bound for their literal tail covers the full prefix. -/
theorem declaration_prefix (code) (n : Nat) (program : ProgHOL 64) (price : Nat)
    (priced : Bound code (dropDeclarations n program) price) : Bound code program price := by
  induction n generalizing program with
  | zero=>exact priced
  | succ n ih=>
    cases program <;> try exact priced
    case dec name shape expression rest=>
      exact declared code name shape expression rest price (ih rest priced)

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.declaration_prefix
