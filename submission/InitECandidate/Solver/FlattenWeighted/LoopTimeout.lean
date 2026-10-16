import InitECandidate.Solver.FlattenWeighted.BasicTimeout
import InitECandidate.Solver.FlattenWeighted.LoopClockRank

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemControl

private theorem exitLoop_timeout {width : Nat} [NeZero width]
    (result : Option (StackSemResult width)) :
    StackSemControl.exitLoop result = some .timeOut → result = some .timeOut := by
  cases result with
  | none => simp [StackSemControl.exitLoop]
  | some result =>
    cases result <;> simp [StackSemControl.exitLoop]

/-- A loop whose body leaves zero clock on timeout has the same property. -/
theorem loopTimeoutClock {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (bodyZero : ∀ source : StackSemStateFiniteExact width C F,
      (evaluate (body, source)).1 = some .timeOut → (evaluate (body, source)).2.clock = 0)
    (source : StackSemStateFiniteExact width C F)
    (timeout : (evaluate (.loop body, source)).1 = some .timeOut) :
    (evaluate (.loop body, source)).2.clock = 0 := by
  have all : ∀ n (state : StackSemStateFiniteExact width C F), state.clock = n →
      (evaluate (.loop body, state)).1 = some .timeOut →
      (evaluate (.loop body, state)).2.clock = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro state ranked timedOut
      have firstZero := bodyZero state
      rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at timedOut ⊢
      rcases execution : evaluate (body, state) with ⟨result, post⟩
      rw [execution] at timedOut firstZero
      have clockLe := StackSemEvaluateClock.evaluateClock body state result post execution
      by_cases continues : contLoop result = true
      · simp only [continues, if_true] at timedOut ⊢
        by_cases zero : post.clock = 0
        · simp [zero, emptyEnv]
        · simp only [zero, if_false] at timedOut ⊢
          exact ih (decClock post).clock (by simp only [decClock]; omega)
            (decClock post) rfl timedOut
      · simp only [continues, if_false, Prod.fst, Prod.snd] at timedOut ⊢
        exact firstZero (exitLoop_timeout result timedOut)
  exact all source.clock source rfl timeout

/-- Any consumed-clock bound that is strictly below the initial clock rules
out timeout. This supplies a concrete starting clock without subtracting a
clock from an existential terminating execution. -/
theorem basicLoop_noTimeout {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (supported : basic body = true)
    (source : StackSemStateFiniteExact width C F) (bound : Nat)
    (consumed : source.clock ≤ (evaluate (.loop body, source)).2.clock + bound)
    (enough : bound < source.clock) :
    (evaluate (.loop body, source)).1 ≠ some .timeOut := by
  intro timeout
  have zero := loopTimeoutClock body (fun state => basicTimeoutClock body state supported) source timeout
  omega

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.loopTimeoutClock
#print axioms InitECandidate.Solver.FlattenWeighted.basicLoop_noTimeout
