import InitECandidate.Solver.Input.NoneControl

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actual escaping sequence exception comes from its genuine first
execution or its actual continuation after a fall-through first result. -/
theorem sequence_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.seq first second) = (some (.exception identifier payload), post)) :
    evaluateHOLFiniteState source first = (some (.exception identifier payload), post) ∨
    ∃ middle, evaluateHOLFiniteState source first = (none, middle) ∧
      evaluateHOLFiniteState middle second = (some (.exception identifier payload), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  generalize computed : evaluateHOLFiniteState source first = output at run ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none => exact Or.inr ⟨middle, rfl, run⟩
  | some result =>
    cases result with
    | exception actualId actualPayload => exact Or.inl run
    | returned value => cases run
    | error => cases run
    | timeOut => cases run
    | «break» => cases run
    | «continue» => cases run
    | finalFfi event => cases run

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.sequence_exception
