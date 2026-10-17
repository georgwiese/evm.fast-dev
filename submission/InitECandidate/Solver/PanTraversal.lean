import InitECandidate.Solver.PanState

/-! Syntax traversal shared by proofs of the unchanged Pancake routines. -/
namespace InitECandidate.Solver.WitnessRadix.BuildProgram
open Flapjack Flapjack.Pancake.PanLang

def loops : ProgHOL 64 → List (ProgHOL 64)
  | .while condition body => .while condition body :: loops body
  | .dec _ _ _ body | .decCall _ _ _ _ body => loops body
  | .seq left right | .ite _ left right => loops left ++ loops right
  | _ => []

end InitECandidate.Solver.WitnessRadix.BuildProgram
