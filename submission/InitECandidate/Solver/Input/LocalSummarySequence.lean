import InitECandidate.Solver.Input.LocalLoopSummary

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Compose actual local summaries, retaining every stopping outcome. -/
theorem local_summary_sequence {F : Type} (key : MlS) (first second : ProgHOL 64)
    (front : ∀ source : PanSemStateFiniteExact 64 F,LocalSummary key first source)
    (back : ∀ source : PanSemStateFiniteExact 64 F,LocalSummary key second source)
    (source : PanSemStateFiniteExact 64 F) : LocalSummary key (.seq first second) source := by
  have info := front source
  unfold LocalSummary at info ⊢
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at info ⊢
  obtain ⟨result,middle⟩ := output
  cases result with
  | none =>
    have tail := back middle
    unfold LocalSummary at tail
    exact ⟨fun normal => (tail.1 normal).trans (info.1 rfl),tail.2⟩
  | some result =>
    refine ⟨?_,info.2⟩
    intro impossible
    cases impossible


end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.local_summary_sequence
