import InitECandidate.Solver.Input.ControlContinue

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actual ordinary sequence outcome exposes the first computation's
ordinary control result, without assuming that computation finishes normally.
Once the concrete first computation proves normal, the real tail follows. -/
theorem sequence_control_first {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (result : Option (PanSemResultExact 64)) (control : ControlResult result)
    (run : evaluateHOLFiniteState source (.seq first second) = (result, target)) :
    ∃ middle firstResult, evaluateHOLFiniteState source first = (firstResult, middle) ∧ ControlResult firstResult ∧
      (firstResult = none → evaluateHOLFiniteState middle second = (result, target)) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  generalize computed : evaluateHOLFiniteState source first = output at run
  obtain ⟨firstResult, middle⟩ := output
  cases firstResult with
  | none => exact ⟨middle, none, rfl, .next, fun _ => run⟩
  | some firstResult =>
    have same := congrArg Prod.fst run
    change some firstResult = result at same
    exact ⟨middle, some firstResult, rfl, same.symm ▸ control, fun impossible => by cases impossible⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.sequence_control_first
