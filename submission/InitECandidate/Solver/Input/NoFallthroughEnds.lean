import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A syntactic return at the end of ordinary scopes/sequences prevents
fallthrough, including errors or failed child calls on the way to it. -/
def endsInReturn : ProgHOL 64→Bool
  | .return _=>true
  | .seq _ rest=>endsInReturn rest
  | .dec _ _ _ rest=>endsInReturn rest
  | .decCall _ _ _ _ rest=>endsInReturn rest
  | _=>false

theorem NoFallthrough.of_ends_in_return (program : ProgHOL 64) (finished : endsInReturn program=true) : NoFallthrough program := by
  cases program with
  | «return» expression=>exact NoFallthrough.returned expression
  | seq first second=>exact NoFallthrough.sequence first second (NoFallthrough.of_ends_in_return second finished)
  | dec name shape expression rest=>exact NoFallthrough.declared name shape expression rest (NoFallthrough.of_ends_in_return rest finished)
  | decCall name shape function arguments rest=>exact NoFallthrough.scoped name shape function arguments rest (NoFallthrough.of_ends_in_return rest finished)
  | _=>simp [endsInReturn] at finished

termination_by structural program

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.NoFallthrough.of_ends_in_return
