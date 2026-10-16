import InitECandidate.Solver.FlattenWeighted.BlockBound
import InitECandidate.Solver.FlattenWeighted.ClockAgreement

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate

/-- A composed block bound supplies an equivalent execution at clocks+1,
provided its entry invariant does not depend on the initial clock. -/
theorem BlockBound.boundedExecution {width : Nat} [NeZero width] {C F : Type}
    {prog : HolProg width} {pre postcondition : StackSemStateFiniteExact width C F → Prop}
    {credits clocks : Nat} (bound : BlockBound prog pre postcondition credits clocks)
    (stable : ∀ state clock, pre state → pre {state with clock := clock})
    (source post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (valid : pre source) (execution : evaluate (prog, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (prog, {source with clock := clocks + 1}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work prog {source with clock := clocks + 1} credits := by
  have nextValid := stable source (clocks + 1) valid
  have consumed := bound.clock {source with clock := clocks + 1} nextValid
  rcases nextRun : evaluate (prog, {source with clock := clocks + 1}) with ⟨nextResult, nextPost⟩
  have nextNotTimeout : nextResult ≠ some .timeOut := by
    intro timedOut
    have run := nextRun
    rw [timedOut] at run
    have zero := bound.timeout {source with clock := clocks + 1} nextPost nextValid run
    rw [nextRun] at consumed
    dsimp only at consumed
    omega
  obtain ⟨sameResult, sameState⟩ := reclockAgreement prog source (clocks + 1)
    result nextResult post nextPost execution nextRun notTimeout nextNotTimeout
  refine ⟨nextPost, ?_, sameState.symm, bound.work _ nextValid⟩
  simpa only [sameResult] using nextRun

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.BlockBound.boundedExecution
