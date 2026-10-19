import InitECandidate.Solver.Input.ExceptionControl

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem sequence_exception_after (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (excluded : (evaluateHOLFiniteState source first).1 ≠ some (.exception identifier payload))
    (run : evaluateHOLFiniteState source (.seq first second) = (some (.exception identifier payload), post)) :
    ∃ middle, evaluateHOLFiniteState source first = (none, middle) ∧
      evaluateHOLFiniteState middle second = (some (.exception identifier payload), post) := by
  rcases sequence_exception source post first second identifier payload run with raised | continued
  · exact (excluded (congrArg Prod.fst raised)).elim
  · exact continued

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.sequence_exception_after
