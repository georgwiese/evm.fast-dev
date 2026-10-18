import InitECandidate.Solver.Input.LocalEffectsScoped

namespace InitECandidate.Solver.Input.LocalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Pancake's primitive word operations update one local result only. -/
theorem primitive (code) (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL 64)) :
    Preserves code (.primitive name operator arguments) := by
  intro source installed
  rw [evaluateHOLFiniteState_primitive]
  repeat first | rfl | split

end InitECandidate.Solver.Input.LocalEffects

#print axioms InitECandidate.Solver.Input.LocalEffects.primitive
