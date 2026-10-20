import InitECandidate.Solver.Input.MainErrorProgram
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input.Main.ErrorHandler
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Main's literal catch handler cannot fall through into its success path,
including on malformed helper results or failed shared-memory effects. -/
theorem stopped : NoFallthrough DecoderCall.handler := by
  rw [original_shape]
  apply NoFallthrough.scoped
  apply NoFallthrough.sequence
  apply NoFallthrough.sequence
  exact NoFallthrough.sequence _ _ (NoFallthrough.returned _)

end InitECandidate.Solver.Input.Main.ErrorHandler

#print axioms InitECandidate.Solver.Input.Main.ErrorHandler.stopped
