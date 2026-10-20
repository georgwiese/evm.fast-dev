import InitECandidate.Solver.Input.NoReturn

namespace InitECandidate.Solver.Input.NoReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An ordinary ignored-result call handles a callee return as fallthrough;
it cannot itself return from its enclosing function. -/
theorem ignored_call (function : MlS) (arguments : List (ExpHOL 64)) : Never (.call (some (none,none)) function arguments) := by
  intro F source value
  classical
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp [args]
  | some values =>
    simp only [args]
    cases lookup : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp [lookup]
    | some data =>
      obtain ⟨body,callee,shape⟩ := data
      simp only [lookup]
      by_cases zero : source.clock = 0
      · simp [zero]
      · simp only [if_neg zero]
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body with
        | mk result post =>
          cases result with
          | none => simp
          | some result =>
            cases result <;> simp
            split <;> simp

end InitECandidate.Solver.Input.NoReturn

#print axioms InitECandidate.Solver.Input.NoReturn.ignored_call
