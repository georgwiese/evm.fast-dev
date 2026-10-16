import InitECandidate.Solver.FlattenWeighted.Work

/-! Turning a decreasing source-state rank into a concrete work budget.
The body budget and rank preservation/decrease must be proved for the actual
source loop; this theorem does not assume a target execution. -/
namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang

/-- At most rank+1 body executions: a final body may exit without reentry. -/
theorem loopWorkOfRank {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (invariant : StackSemStateFiniteExact width C F → Prop)
    (rank : StackSemStateFiniteExact width C F → Nat) (perBody : Nat)
    (bodyWork : ∀ state, invariant state → Work body state perBody)
    (decreases : ∀ state post result, invariant state →
      StackSemEvaluate.evaluate (body, state) = (result, post) →
      StackSemControl.contLoop result = true → post.clock ≠ 0 →
      invariant (StackSemStateOps.decClock post) ∧
        rank (StackSemStateOps.decClock post) < rank state)
    (source : StackSemStateFiniteExact width C F) (valid : invariant source) :
    Work (.loop body) source ((rank source + 1) * perBody) := by
  have all : ∀ n state, rank state = n → invariant state →
      Work (.loop body) state ((rank state + 1) * perBody) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro state ranked valid
      have again : ∀ post result, StackSemEvaluate.evaluate (body, state) = (result, post) →
          StackSemControl.contLoop result = true → post.clock ≠ 0 →
          Work (.loop body) (StackSemStateOps.decClock post) (rank state * perBody) := by
        intro post result execution continues nonzero
        obtain ⟨nextValid, less⟩ := decreases state post result valid execution continues nonzero
        have next := ih _ (by omega) _ rfl nextValid
        apply Work.mono (derivation := next)
        apply Nat.mul_le_mul_right perBody
        omega
      have total := Work.loop (bodyWork state valid) again
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using total
  exact all _ source rfl valid

/-- The rank bound supplies the original quantitative flattening simulation. -/
theorem loopPaidOfRank {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (invariant : StackSemStateFiniteExact width C F → Prop)
    (rank : StackSemStateFiniteExact width C F → Nat) (perBody : Nat)
    (bodyWork : ∀ state, invariant state → Work body state perBody)
    (decreases : ∀ state post result, invariant state →
      StackSemEvaluate.evaluate (body, state) = (result, post) →
      StackSemControl.contLoop result = true → post.clock ≠ 0 →
      invariant (StackSemStateOps.decClock post) ∧
        rank (StackSemStateOps.decClock post) < rank state)
    (source : StackSemStateFiniteExact width C F) (valid : invariant source) :
    PaidProp ((rank source + 1) * perBody) (.loop body) source :=
  workPaid (loopWorkOfRank body invariant rank perBody bodyWork decreases source valid)

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.loopWorkOfRank
#print axioms InitECandidate.Solver.FlattenWeighted.loopPaidOfRank
