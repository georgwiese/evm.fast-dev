import InitECandidate.Solver.Input.CallPrefixTrace
import InitECandidate.Solver.Input.NoReturnAtoms

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuinely returning enclosing body must pass every lexical prefix
action when that prefix itself cannot return. This needs no supplied
helper successes or quantitative bound. -/
theorem normal_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (actions : List Action) (tail : ProgHOL 64)
    (value : ValueHOL 64) (never : NoReturn.Never (program actions .skip))
    (normal : evaluateHOLFiniteState source (program actions tail)=(some (.returned value),post)) :
    ∃ current inner,Execution source actions current ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current tail=(some (.returned value),inner) := by
  rcases classify source actions with stopped|reached
  · have result:=congrArg Prod.fst (stopped tail)
    rw [normal] at result
    exact (never source value result.symm).elim
  · obtain ⟨current,execution⟩:=reached
    have replay:=execution.project tail
    rw [normal] at replay
    have result:=congrArg Prod.fst replay
    have clock:=congrArg Prod.snd replay
    exact ⟨current,(evaluateHOLFiniteState current tail).2,execution,clock,Prod.ext result.symm rfl⟩

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.normal_trace
