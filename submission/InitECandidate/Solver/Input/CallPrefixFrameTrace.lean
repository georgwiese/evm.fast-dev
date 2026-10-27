import InitECandidate.Solver.Input.CallPrefixNormalTrace

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuine enclosing return passes every nonreturning lexical action.
The actual continuation retains all nonlocal state and the observed clock. -/
theorem normal_frame_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (actions : List Action)
    (tail : ProgHOL 64) (value : ValueHOL 64) (never : NoReturn.Never (program actions .skip))
    (actual : evaluateHOLFiniteState source (program actions tail) = (some (.returned value), post)) :
    ∃ current inner, Execution source actions current ∧
      evaluateHOLFiniteState current tail = (some (.returned value), inner) ∧
      post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner := by
  rcases classify_frame source actions with stopped | reached
  · have same := congrArg (fun observed => observed.1.1) (stopped tail)
    rw [actual] at same
    exact (never source value same.symm).elim
  · obtain ⟨current, execution⟩ := reached
    have same := execution.observe tail
    rw [actual] at same
    have result := congrArg (fun observed => observed.1.1) same
    exact ⟨current, (evaluateHOLFiniteState current tail).2, execution, Prod.ext result.symm rfl,
      congrArg (fun observed => observed.1.2) same, congrArg Prod.snd same⟩

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.normal_frame_trace
