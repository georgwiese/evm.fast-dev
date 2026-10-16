import InitECandidate.Solver.FlattenWeighted.LoopRank

/-! The same source-state rank bounds consumed Stack clock as well as extra
flattening work. These are separate quantities in the source semantics. -/
namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate

/-- The rank bounds body clock consumption plus each loop reentry clock.
The final unused clock is retained, so this statement does not presume a
minimal-clock source execution. -/
theorem loopClockOfRank {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (invariant : StackSemStateFiniteExact width C F → Prop)
    (rank : StackSemStateFiniteExact width C F → Nat) (perBody : Nat)
    (bodyClock : ∀ state, invariant state →
      state.clock ≤ (evaluate (body, state)).2.clock + perBody)
    (decreases : ∀ state post result, invariant state →
      evaluate (body, state) = (result, post) →
      StackSemControl.contLoop result = true → post.clock ≠ 0 →
      invariant (StackSemStateOps.decClock post) ∧
        rank (StackSemStateOps.decClock post) < rank state)
    (source : StackSemStateFiniteExact width C F) (valid : invariant source) :
    source.clock ≤ (evaluate (.loop body, source)).2.clock +
      (rank source + 1) * (perBody + 1) := by
  have all : ∀ n state, rank state = n → invariant state →
      state.clock ≤ (evaluate (.loop body, state)).2.clock +
        (rank state + 1) * (perBody + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro state ranked valid
      have first := bodyClock state valid
      rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]
      rcases execution : evaluate (body, state) with ⟨result, post⟩
      rw [execution] at first
      dsimp only at first ⊢
      have oneBody : perBody + 1 ≤ (rank state + 1) * (perBody + 1) := by
        have scaled := Nat.mul_le_mul_right (perBody + 1) (show 1 ≤ rank state + 1 by omega)
        simpa only [Nat.one_mul] using scaled
      by_cases continues : StackSemControl.contLoop result = true
      · rw [if_pos continues]
        by_cases nonzero : post.clock = 0
        · rw [if_pos nonzero]
          simp only [StackSemStateOps.emptyEnv, Prod.snd]
          omega
        · rw [if_neg nonzero]
          obtain ⟨nextValid, less⟩ := decreases state post result valid execution continues nonzero
          have next := ih _ (by omega) _ rfl nextValid
          have scaled := Nat.mul_le_mul_right (perBody + 1)
            (show rank (StackSemStateOps.decClock post) + 1 + 1 ≤ rank state + 1 by omega)
          have enough : (rank (StackSemStateOps.decClock post) + 1) * (perBody + 1) +
              (perBody + 1) ≤ (rank state + 1) * (perBody + 1) := by
            simpa only [Nat.add_mul, Nat.one_mul] using scaled
          have postClock : (StackSemStateOps.decClock post).clock = post.clock - 1 := rfl
          omega
      · rw [if_neg continues]
        dsimp only
        omega
  exact all _ source rfl valid

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.loopClockOfRank
