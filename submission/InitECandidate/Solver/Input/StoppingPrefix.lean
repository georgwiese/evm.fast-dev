import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem NoFallthrough.returning_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : ProgHOL 64) (stops : NoFallthrough first) (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.seq first second) = (some (.returned returned), post)) :
    evaluateHOLFiniteState source first = (some (.returned returned), post) := by
  have cannot := stops source
  rw [evaluateHOLFiniteState_seq_line780] at run
  generalize computed : evaluateHOLFiniteState source first = output at cannot run ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none => exact (cannot rfl).elim
  | some result => exact run

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.NoFallthrough.returning_prefix
