import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- Loop-free and call-free code has a syntax-bounded clock cost. -/
def straight {width : Nat} [NeZero width] : HolLoopProg width → Bool
  | .seq first second | .ite _ _ _ first second _ => straight first && straight second
  | .mark body => straight body
  | .loop .. | .call .. => false
  | _ => true

def charge {width : Nat} [NeZero width] : HolLoopProg width → Nat
  | .seq first second => charge first + charge second
  | .ite _ _ _ first second _ => max (charge first) (charge second) + 1
  | .mark body => charge body
  | .tick => 1
  | _ => 0

theorem cutResClockBudget {width : Nat} [NeZero width] {F : Type}
    (live : NumSet) (step : Option (LoopResultExact width) × LoopSemStateFiniteExact width F) :
    step.2.clock ≤ (cutRes live step).2.clock + 1 := by
  obtain ⟨result, source⟩ := step
  cases result with
  | some _ => simp [cutRes]
  | none =>
    simp only [cutRes]
    cases cut : cutState live source with
    | none => simp
    | some post =>
      have same := cutState_clock cut
      simp only
      split <;> simp only [decClock] <;> omega

/-- Bound consumed clock for every execution, including failure and timeout.
This is independent of the compiler's expression-preservation proof. -/
theorem straightClock {width : Nat} [NeZero width] {F : Type}
    (program : HolLoopProg width) (source : LoopSemStateFiniteExact width F)
    (supported : straight program = true) :
    source.clock ≤ (evaluate program source).2.clock + charge program := by
  cases program with
  | seq first second =>
    have both : straight first = true ∧ straight second = true := by
      simpa only [straight, Bool.and_eq_true] using supported
    obtain ⟨ok1, ok2⟩ := both
    have bound1 := straightClock first source ok1
    have bound2 := straightClock second (evaluate first source).2 ok2
    rw [evaluate, fix_clock_evaluate]
    rcases run : evaluate first source with ⟨result, post⟩
    simp only [run] at bound1 bound2
    cases result <;> simp only [charge] at * <;> omega
  | ite cmp register operand first second live =>
    have both : straight first = true ∧ straight second = true := by
      simpa only [straight, Bool.and_eq_true] using supported
    obtain ⟨ok1, ok2⟩ := both
    have bound1 := straightClock first source ok1
    have bound2 := straightClock second source ok2
    have cut1 := cutResClockBudget live (evaluate first source)
    have cut2 := cutResClockBudget live (evaluate second source)
    simp only [charge]
    rw [evaluate]
    split <;> (try split) <;> (try dsimp only) <;> omega
  | mark body =>
    simpa only [evaluate, charge] using straightClock body source supported
  | loop _ _ _ => simp [straight] at supported
  | call _ _ _ _ => simp [straight] at supported
  | _ =>
    simp only [charge]
    rw [evaluate]
    all_goals (repeat' split)
    all_goals (try simp only [LoopSemStateFiniteExact.setVar, LoopSemStateFiniteExact.setVars,
      LoopSemStateFiniteExact.setGlobals, LoopSemStateFiniteExact.callEnv,
      LoopSemStateFiniteExact.decClock, LoopSemStateFiniteExact.shMemOp_clock, Prod.snd])
    all_goals (try have same := memStore_clock ‹_›)
    all_goals (try have same := loopArith_clock ‹_›)
    all_goals (try have same := cutState_clock ‹_›)
    all_goals (try dsimp only at *)
    all_goals omega
termination_by sizeOf program

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.cutResClockBudget
#print axioms InitECandidate.Solver.CrepToLoopBound.straightClock
