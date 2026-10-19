import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Invert a real returning sequence when its front cannot itself return.
Both actual runs, including the front's normal state, are derived. -/
theorem sequence_returned {F : Type} (source target : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    (value : ValueHOL 64) (never : ∀ returned,(evaluateHOLFiniteState source first).1≠some (.returned returned))
    (normal : evaluateHOLFiniteState source (.seq first second)=(some (.returned value),target)) :
    ∃ middle,evaluateHOLFiniteState source first=(none,middle) ∧
      evaluateHOLFiniteState middle second=(some (.returned value),target) := by
  rw [evaluateHOLFiniteState_seq_line780] at normal
  generalize computed : evaluateHOLFiniteState source first=output at normal never
  obtain ⟨result,middle⟩ := output
  cases result with
  | none => exact ⟨middle,rfl,normal⟩
  | some result =>
    have actual : result=.returned value := Option.some.inj (congrArg Prod.fst normal)
    subst result
    exact (never value rfl).elim

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.sequence_returned
