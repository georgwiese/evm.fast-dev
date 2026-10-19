import InitECandidate.Solver.Input.NoReturnScoped

namespace InitECandidate.Solver.Input.NoReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem caught_destination (destination : Option (VarKind × MlS)) (function : MlS) (arguments : List (ExpHOL 64)) (identifier parameter : MlS)
    (handler : ProgHOL 64) (tail : Never handler) :
    Never (.call (some (destination,some (identifier,parameter,handler))) function arguments) := by
  intro F source value
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]; simp
  | some values =>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]; simp
    | some data =>
      obtain ⟨body,callee,shape⟩ := data
      simp only [called]
      by_cases zero : source.clock=0
      · simp [zero]
      · rw [if_neg zero]
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output
        obtain ⟨result,target⟩ := output
        cases result with
        | none => simp
        | some result =>
          cases result with
          | returned answer =>
            simp only
            split
            · cases destination with
              | none => simp
              | some target => simp only; split <;> simp
            · simp
          | exception exceptionId payload =>
            simp only
            split
            · split
              · split
                · exact tail _ value
                · simp
              · simp
            · simp
          | error => simp
          | timeOut => simp
          | «break» => simp
          | «continue» => simp
          | finalFfi event => simp

/-- Ignored-result specialization of the common caught-call rule. -/
theorem caught_call (function : MlS) (arguments : List (ExpHOL 64)) (identifier parameter : MlS)
    (handler : ProgHOL 64) (tail : Never handler) :
    Never (.call (some (none,some (identifier,parameter,handler))) function arguments) :=
  caught_destination none function arguments identifier parameter handler tail

end InitECandidate.Solver.Input.NoReturn

#print axioms InitECandidate.Solver.Input.NoReturn.caught_call

#print axioms InitECandidate.Solver.Input.NoReturn.caught_destination
