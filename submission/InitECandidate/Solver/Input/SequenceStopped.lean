import InitECandidate.Solver.Input.NoneControl

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem sequence_stopped {F : Type} (source : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    (stopped : (evaluateHOLFiniteState source first).1 ≠ none) :
    evaluateHOLFiniteState source (.seq first second) = evaluateHOLFiniteState source first := by
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at stopped ⊢
  obtain ⟨result, post⟩ := output
  cases result with
  | none => exact (stopped rfl).elim
  | some result => rfl

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.sequence_stopped
