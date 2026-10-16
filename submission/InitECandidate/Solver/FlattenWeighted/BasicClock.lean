import InitECandidate.Solver.FlattenWeighted.Straight
import InitECandidate.Solver.FlattenWeighted.Common

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Solver.FlattenBound
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

/-- Basic instruction blocks whose only clock-consuming leaf is Tick. -/
def basic {width : Nat} [NeZero width] : HolProg width → Bool
  | .seq first second | .ite _ _ _ first second => basic first && basic second
  | .skip | .inst _ | .tick | .ret _ | .halt _ | .locValue _ _ _ => true
  | _ => false

def ticks {width : Nat} [NeZero width] : HolProg width → Nat
  | .seq first second => ticks first + ticks second
  | .ite _ _ _ first second => max (ticks first) (ticks second)
  | .tick => 1
  | _ => 0

theorem basic_straight {width : Nat} [NeZero width] (prog : HolProg width)
    (supported : basic prog = true) : straight prog = true := by
  cases prog with
  | seq first second | ite _ _ _ first second =>
    have both : basic first = true ∧ basic second = true := by simpa [basic] using supported
    simp only [straight, basic_straight first both.1, basic_straight second both.2, Bool.and_self]
  | _ => simp_all [basic, straight]
termination_by sizeOf prog

theorem basicClock {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (source : StackSemStateFiniteExact width C F)
    (supported : basic prog = true) :
    source.clock ≤ (evaluate (prog, source)).2.clock + ticks prog := by
  cases prog with
  | seq first second =>
    have both : basic first = true ∧ basic second = true := by simpa [basic] using supported
    have hfirst := basicClock first source both.1
    have hsecond := basicClock second (evaluate (first, source)).2 both.2
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
    rcases run : evaluate (first, source) with ⟨result, post⟩
    rw [run] at hfirst hsecond
    cases result <;> simp only [ticks, Prod.snd] at * <;> omega
  | ite cmp register operand first second =>
    have both : basic first = true ∧ basic second = true := by simpa [basic] using supported
    have hfirst := basicClock first source both.1
    have hsecond := basicClock second source both.2
    rw [evaluate_ite]
    simp only [ticks]
    repeat' split
    all_goals (try dsimp only)
    all_goals omega
  | inst instruction =>
    rw [evaluate_inst]
    cases run : StackSemInst.instHOL instruction source with
    | none => simp [ticks]
    | some post =>
      have same := StackSemInst.instHOL_clock_eq instruction source post run
      simp only [ticks, Prod.snd]
      omega
  | skip => simp [evaluate_skip, ticks]
  | halt register =>
    rw [evaluate_halt]
    split <;> simp [ticks, StackSemStateOps.emptyEnv]
  | ret register =>
    rw [evaluate_ret]
    split <;> simp [ticks]
  | tick =>
    rw [evaluate_tick]
    split <;> simp only [ticks, StackSemStateOps.emptyEnv, StackSemStateOps.decClock, Prod.snd] <;> omega
  | locValue register first second =>
    rw [evaluate_locValue]
    split <;> simp [ticks, StackSemStateOps.setVar]
  | _ => simp [basic] at supported
termination_by sizeOf prog

/-- A constant bound for any basic block, including timeout/error branches
in the source-clock estimate and every original flattening hypothesis. -/
theorem basicPaid {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (source : StackSemStateFiniteExact width C F)
    (supported : basic prog = true) : PaidProp (ticks prog + nodes prog) prog source := by
  intro tail result post name label continues breaks target hypotheses
  have consumed := basicClock prog source supported
  rw [hypotheses.1] at consumed
  apply paidOfBounded (limit := 0)
  · simp only [budget, Nat.zero_add, Nat.one_mul]
    dsimp only at consumed
    omega
  · exact straightBounded prog source (basic_straight prog supported)
      tail result post name label continues breaks target hypotheses

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.basic_straight
#print axioms InitECandidate.Solver.FlattenWeighted.basicClock
#print axioms InitECandidate.Solver.FlattenWeighted.basicPaid
