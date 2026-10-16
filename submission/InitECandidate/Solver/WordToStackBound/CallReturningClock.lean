import InitECandidate.Solver.WordToStackBound.CallReturningHistory

namespace InitECandidate.Solver.WordToStackBound.CallReturning
open Flapjack
open Flapjack.WordToStackProofs.CompCorrect.CallReturning

theorem sourceCallTailClock {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost)) : sourcePost.clock ≤ bodyPost.clock := by
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  cases bodyResult with
  | none => obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution; exact Nat.le_refl _
  | some bodyResult =>
    cases bodyResult <;> try (obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution; exact Nat.le_refl _)
    case result location returned =>
      simp only at execution
      by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
      · rw [if_pos invalid] at execution
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
        exact Nat.le_refl _
      rw [if_neg invalid] at execution
      cases pop : WordSemStateFiniteExact.popEnv bodyPost with
      | none =>
        rw [pop] at execution
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
        exact Nat.le_refl _
      | some popped =>
        rw [pop] at execution
        simp only at execution
        have clockEq := WordSemStateFiniteExact.popEnv_clock bodyPost popped pop
        by_cases domain : sptDomainEqUnion popped.locals envs.1 envs.2
        · rw [if_pos domain] at execution
          have bound := (WordSemStateFiniteExact.evaluate_clock retCode
            (WordSemStateFiniteExact.setVars values returned popped) result sourcePost execution).1
          simpa only [WordSemStateFiniteExact.setVars, clockEq] using bound
        · rw [if_neg domain] at execution
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
          exact clockEq.le

end InitECandidate.Solver.WordToStackBound.CallReturning
#print axioms InitECandidate.Solver.WordToStackBound.CallReturning.sourceCallTailClock
