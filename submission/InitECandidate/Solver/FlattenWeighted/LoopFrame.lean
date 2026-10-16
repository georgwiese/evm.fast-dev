import InitECandidate.Solver.FlattenWeighted.BasicClock

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemControl

/-- Lift preservation of any clock-independent state observation through an
actual loop. Timeout may clear registers, so only non-timeout exits are covered. -/
theorem loopFrame {width : Nat} [NeZero width] {C F A : Type}
    (body : HolProg width) (observe : StackSemStateFiniteExact width C F → A)
    (stable : ∀ state, observe (decClock state) = observe state)
    (bodyFrame : ∀ state,
      (evaluate (body, state)).1 ≠ some .timeOut →
      observe (evaluate (body, state)).2 = observe state)
    (source : StackSemStateFiniteExact width C F)
    (notTimeout : (evaluate (.loop body, source)).1 ≠ some .timeOut) :
    observe (evaluate (.loop body, source)).2 = observe source := by
  have all : ∀ n (state : StackSemStateFiniteExact width C F), state.clock = n →
      (evaluate (.loop body, state)).1 ≠ some .timeOut →
      observe (evaluate (.loop body, state)).2 = observe state := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro state ranked notTimed
      rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at notTimed ⊢
      rcases run : evaluate (body, state) with ⟨result, post⟩
      rw [run] at notTimed
      have clockLe := StackSemEvaluateClock.evaluateClock body state result post run
      have frame := bodyFrame state
      rw [run] at frame
      dsimp only at frame
      by_cases continues : contLoop result = true
      · have bodyNot : result ≠ some .timeOut := by
          intro equal
          rw [equal] at continues
          simp [contLoop] at continues
        have same := frame bodyNot
        simp only [continues, if_true] at notTimed ⊢
        by_cases zero : post.clock = 0
        · simp [zero] at notTimed
        · simp only [zero, if_false] at notTimed ⊢
          exact (ih (decClock post).clock (by simp only [decClock]; omega)
            (decClock post) rfl notTimed).trans ((stable post).trans same)
      · simp only [continues, Bool.false_eq_true, if_false, Prod.fst, Prod.snd] at notTimed ⊢
        apply frame
        intro equal
        rw [equal] at notTimed
        exact notTimed rfl
  exact all source.clock source rfl notTimeout

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.loopFrame
