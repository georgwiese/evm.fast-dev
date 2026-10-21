import InitECandidate.Solver.Input.PureDecision

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuine read-only decision either stops without source-clock spending
or enters its actual continuation at the unchanged state. -/
theorem PureDecision.trace {first : ProgHOL 64} (decision : PureDecision first)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (continuation : ProgHOL 64)
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.seq first continuation)=(outcome,post)) :
    source.clock=post.clock ∨ evaluateHOLFiniteState source continuation=(outcome,post) := by
  have summary:=decision.summary source
  have quiet:=decision.quiet source.code source rfl
  rw [evaluateHOLFiniteState_seq_line780] at run
  generalize computed : evaluateHOLFiniteState source first=output at summary quiet run
  obtain ⟨answer,middle⟩ := output
  cases answer with
  | none =>
    have same : middle=source := summary.1 rfl
    subst middle
    exact Or.inr run
  | some answer =>
    have endpoint : middle=post := congrArg Prod.snd run
    exact Or.inl (quiet.symm.trans (congrArg PanSemStateFiniteExact.clock endpoint))

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.PureDecision.trace
