import InitECandidate.Solver.FlattenWeighted.BasicClock

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate

/-- In a basic block a timeout can only originate at a tick with zero clock. -/
theorem basicTimeoutClock {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (source : StackSemStateFiniteExact width C F)
    (supported : basic prog = true)
    (timeout : (evaluate (prog, source)).1 = some .timeOut) :
    (evaluate (prog, source)).2.clock = 0 := by
  cases prog with
  | seq first second =>
    have both : basic first = true ∧ basic second = true := by simpa [basic] using supported
    have hfirst := basicTimeoutClock first source both.1
    have hsecond := basicTimeoutClock second (evaluate (first, source)).2 both.2
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at timeout ⊢
    rcases run : evaluate (first, source) with ⟨result, post⟩
    rw [run] at hfirst hsecond timeout
    cases result with
    | none => exact hsecond timeout
    | some result => exact hfirst timeout
  | ite cmp register operand first second =>
    have both : basic first = true ∧ basic second = true := by simpa [basic] using supported
    have hfirst := basicTimeoutClock first source both.1
    have hsecond := basicTimeoutClock second source both.2
    rw [evaluate_ite] at timeout ⊢
    repeat' split at timeout
    all_goals simp_all
  | inst instruction =>
    rw [evaluate_inst] at timeout
    split at timeout <;> simp_all
  | skip => simp [evaluate_skip] at timeout
  | halt register =>
    rw [evaluate_halt] at timeout
    split at timeout <;> simp_all
  | ret register =>
    rw [evaluate_ret] at timeout
    split at timeout <;> simp_all
  | tick =>
    by_cases zero : source.clock = 0
    · simp [evaluate_tick, zero, StackSemStateOps.emptyEnv]
    · simp [evaluate_tick, zero] at timeout
  | «break» label => simp [evaluate_break] at timeout
  | «continue» label => simp [evaluate_continue] at timeout
  | locValue register first second =>
    rw [evaluate_locValue] at timeout
    split at timeout <;> simp_all
  | _ => simp [basic] at supported
termination_by sizeOf prog

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.basicTimeoutClock
