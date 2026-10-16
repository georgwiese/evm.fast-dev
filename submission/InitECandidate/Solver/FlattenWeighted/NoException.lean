import InitECandidate.Solver.FlattenWeighted.BasicClock

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemControl

/-- Local control flow and instructions cannot originate an exception. Calls,
allocation, foreign operations and explicit raises are deliberately excluded. -/
def noRaise {width : Nat} [NeZero width] : HolProg width → Bool
  | .seq first second | .ite _ _ _ first second => noRaise first && noRaise second
  | .loop body => noRaise body
  | .skip | .inst _ | .tick | .ret _ | .halt _ | .locValue _ _ _ | .break _ | .continue _ => true
  | _ => false

private theorem exitLoop_exception {width : Nat} [NeZero width]
    (result : Option (StackSemResult width)) (value : WordLocW width) :
    StackSemControl.exitLoop result = some (.exception value) → result = some (.exception value) := by
  cases result with
  | none => simp [StackSemControl.exitLoop]
  | some result => cases result <;> simp [StackSemControl.exitLoop]

theorem loopNoException {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (bodySafe : ∀ (state : StackSemStateFiniteExact width C F) value,
      (evaluate (body, state)).1 ≠ some (.exception value))
    (source : StackSemStateFiniteExact width C F) (value : WordLocW width) :
    (evaluate (.loop body, source)).1 ≠ some (.exception value) := by
  have all : ∀ n (state : StackSemStateFiniteExact width C F), state.clock = n →
      (evaluate (.loop body, state)).1 ≠ some (.exception value) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro state ranked raised
      have bodyNot := bodySafe state value
      rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at raised
      rcases execution : evaluate (body, state) with ⟨result, post⟩
      rw [execution] at raised bodyNot
      have clockLe := StackSemEvaluateClock.evaluateClock body state result post execution
      by_cases continues : contLoop result = true
      · simp only [continues, if_true] at raised
        by_cases zero : post.clock = 0
        · simp [zero] at raised
        · simp only [zero, if_false] at raised
          exact ih (decClock post).clock (by simp only [decClock]; omega)
            (decClock post) rfl raised
      · simp only [continues, if_false, Prod.fst] at raised
        exact bodyNot (exitLoop_exception result value raised)
  exact all source.clock source rfl

/-- A structural check excludes exception results for every actual execution,
including malformed registers, failed memory accesses and exhausted clocks. -/
theorem noException {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (supported : noRaise prog = true)
    (source : StackSemStateFiniteExact width C F) (value : WordLocW width) :
    (evaluate (prog, source)).1 ≠ some (.exception value) := by
  cases prog with
  | seq first second =>
    have both : noRaise first = true ∧ noRaise second = true := by simpa [noRaise] using supported
    have hfirst := noException first both.1 source value
    have hsecond := noException second both.2 (evaluate (first, source)).2 value
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
    rcases run : evaluate (first, source) with ⟨result, post⟩
    rw [run] at hfirst hsecond
    cases result with
    | none => exact hsecond
    | some result => exact hfirst
  | ite cmp register operand first second =>
    have both : noRaise first = true ∧ noRaise second = true := by simpa [noRaise] using supported
    have hfirst := noException first both.1 source value
    have hsecond := noException second both.2 source value
    rw [evaluate_ite]
    repeat' split
    all_goals simp_all
  | loop body =>
    exact loopNoException body (fun state value => noException body supported state value) source value
  | inst instruction => rw [evaluate_inst]; split <;> simp_all
  | skip => simp [evaluate_skip]
  | halt register => rw [evaluate_halt]; split <;> simp_all
  | ret register => rw [evaluate_ret]; split <;> simp_all
  | tick => rw [evaluate_tick]; split <;> simp_all
  | «break» label => simp [evaluate_break]
  | «continue» label => simp [evaluate_continue]
  | locValue register first second => rw [evaluate_locValue]; split <;> simp_all
  | _ => simp [noRaise] at supported
termination_by sizeOf prog

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.loopNoException
#print axioms InitECandidate.Solver.FlattenWeighted.noException
