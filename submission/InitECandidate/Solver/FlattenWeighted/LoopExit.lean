import InitECandidate.Solver.FlattenWeighted.LoopRank

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps

private theorem normalExit_break {width : Nat} [NeZero width]
    (result : Option (StackSemResult width))
    (stopped : StackSemControl.contLoop result ≠ true)
    (normal : StackSemControl.exitLoop result = none) : result = some (.break 0) := by
  cases result with
  | none => simp [StackSemControl.contLoop] at stopped
  | some result =>
    cases result <;> simp_all [StackSemControl.exitLoop]

/-- Lift a body invariant and Break-0 postcondition to normal exit of the actual
loop evaluator. No condition is imposed on error/timeout/other control exits. -/
theorem loopNormalExit {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (invariant final : StackSemStateFiniteExact width C F → Prop)
    (preserves : ∀ state post result, invariant state →
      evaluate (body, state) = (result, post) →
      StackSemControl.contLoop result = true → post.clock ≠ 0 → invariant (decClock post))
    (exits : ∀ state post, invariant state →
      evaluate (body, state) = (some (.break 0), post) → final post)
    (source post : StackSemStateFiniteExact width C F) (valid : invariant source)
    (execution : evaluate (.loop body, source) = (none, post)) : final post := by
  have all : ∀ n (state post : StackSemStateFiniteExact width C F), state.clock = n →
      invariant state → evaluate (.loop body, state) = (none, post) → final post := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro state post ranked valid run
      rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at run
      rcases firstRun : evaluate (body, state) with ⟨result, middle⟩
      rw [firstRun] at run
      have clockLe := StackSemEvaluateClock.evaluateClock body state result middle firstRun
      by_cases continues : StackSemControl.contLoop result = true
      · simp only [continues, if_true] at run
        by_cases zero : middle.clock = 0
        · simp [zero] at run
        · simp only [zero, if_false] at run
          exact ih (decClock middle).clock (by simp only [decClock]; omega)
            (decClock middle) post rfl (preserves state middle result valid firstRun continues zero) run
      · simp only [continues, if_false] at run
        have normal : StackSemControl.exitLoop result = none := congrArg Prod.fst run
        have same : middle = post := congrArg Prod.snd run
        have resultEq := normalExit_break result continues normal
        rw [resultEq] at firstRun
        simpa only [same] using exits state middle valid firstRun
  exact all source.clock source post rfl valid execution

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.loopNormalExit
