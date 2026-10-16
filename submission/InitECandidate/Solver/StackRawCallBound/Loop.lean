import InitECandidate.Solver.StackRawCallBound.Common

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.LoopCase

theorem compCorrectLoopExit {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : BoundedProgramIH C F body source)
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target)
    (exit : contLoop result = false) :
    BoundedSimulation 0 (source.clock - post.clock) (comp info (.loop body)) info target post
      (StackSemControl.exitLoop result) := by
  obtain ⟨clock, targetState, stackSpace, budget, postRelation, targetExecution, guard⟩ :=
    bodyIH info target post result ⟨execution, nonerror, relation⟩
  refine ⟨clock, targetState, stackSpace, by omega, postRelation, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclamped, targetExecution]
    simp only [exit, Bool.false_eq_true, if_false]
  · intro exitGuard
    exact guard (exitLoopGuard result exitGuard)

/-- Loop continuation excludes both exceptional stack-space guard results. -/
theorem contLoopGuard {width : Nat} [NeZero width]
    (result : Option (StackSemResult width)) (continuing : contLoop result = true) :
    result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) := by
  rcases Compiler.Backend.StackProps.contLoopImp result continuing with h | h <;>
    simp [h]

/-- The zero-clock continuation branch, with target timeout and relation
both derived from the actual body induction hypothesis. Untagged case support. -/
theorem compCorrectLoopTimeout {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : BoundedProgramIH C F body source)
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target)
    (continuing : contLoop result = true) (zero : post.clock = 0) :
    BoundedSimulation 0 (source.clock - post.clock) (comp info (.loop body)) info target (emptyEnv post)
      (some .timeOut) := by
  obtain ⟨clock, targetState, stackSpace, budget, postRelation, targetExecution, guard⟩ :=
    bodyIH info target post result ⟨execution, nonerror, relation⟩
  have spaceEq := guard (contLoopGuard result continuing)
  subst stackSpace
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  rw [stackSelf] at targetExecution
  have targetZero : targetState.clock = 0 :=
    (stateRel_clock info post targetState postRelation).trans zero
  refine ⟨clock, emptyEnv targetState, (emptyEnv targetState).stackSpace, by omega,
    stateRel_emptyEnv info post targetState postRelation, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclamped, targetExecution]
    simp only [continuing, if_true]
    rw [if_pos targetZero]
  · intro impossible
    exact False.elim (impossible.1 rfl)

/-- The original evaluate_ind Loop reentry IH at the actual body's post-state.
The source body evaluation, continuation and nonzero post-clock guard the
motive at decClock bodyPost; no arbitrary smaller-clock state is quantified. -/
abbrev BoundedLoopReentryIH {width : Nat} [NeZero width] (C F : Type)
    (body : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (bodyResult : Option (StackSemResult width))
    (bodyPost : StackSemStateFiniteExact width C F),
    StackSemEvaluate.evaluate (body, source) = (bodyResult, bodyPost) →
    contLoop bodyResult = true → bodyPost.clock ≠ 0 →
    BoundedProgramIH C F (.loop body) (decClock bodyPost)

/-- Nonzero continuation: extend the actual target body clock by the clock
needed for the smaller recursive Loop execution. All target results are derived
from the two genuine IHs. Untagged case-split infrastructure. -/
theorem compCorrectLoopReentry {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target bodyPost post : StackSemStateFiniteExact width C F)
    (bodyResult result : Option (StackSemResult width))
    (bodyIH : BoundedProgramIH C F body source)
    (reentryIH : BoundedLoopReentryIH C F body source)
    (bodyExecution : StackSemEvaluate.evaluate (body, source) = (bodyResult, bodyPost))
    (bodyNonerror : bodyResult ≠ some .error) (relation : stateRel info source target)
    (continuing : contLoop bodyResult = true) (nonzero : bodyPost.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate (.loop body, decClock bodyPost) = (result, post))
    (nonerror : result ≠ some .error) :
    BoundedSimulation 0 (source.clock - post.clock) (comp info (.loop body)) info target post result := by
  obtain ⟨clock, targetBody, stackSpace, bodyBudget, bodyRelation, targetBodyExecution, bodyGuard⟩ :=
    bodyIH info target bodyPost bodyResult ⟨bodyExecution, bodyNonerror, relation⟩
  have continuationGuard := contLoopGuard bodyResult continuing
  have spaceEq := bodyGuard continuationGuard
  subst stackSpace
  have stackSelf : { targetBody with stackSpace := targetBody.stackSpace } = targetBody := by
    cases targetBody
    rfl
  rw [stackSelf] at targetBodyExecution
  have recursiveRelation := stateRel_decClock info bodyPost targetBody bodyRelation
  obtain ⟨recursiveClock, targetPost, finalSpace, recursiveBudget, postRelation, targetExecution, guard⟩ :=
    reentryIH bodyResult bodyPost bodyExecution continuing nonzero
      info (decClock targetBody) post result
      ⟨execution, nonerror, recursiveRelation⟩
  have targetClockEq := stateRel_clock info bodyPost targetBody bodyRelation
  have targetNonzero : targetBody.clock ≠ 0 := by
    simpa only [targetClockEq] using nonzero
  have extendedBody := Compiler.Backend.StackProps.evaluateAddClock recursiveClock
    (comp info body) { target with clock := target.clock + clock }
    bodyResult targetBody ⟨targetBodyExecution, continuationGuard.1⟩
  have inputEq : { { target with clock := target.clock + clock } with
      clock := ({ target with clock := target.clock + clock }).clock + recursiveClock } =
      { target with clock := target.clock + (clock + recursiveClock) } := by
    simp only [Nat.add_assoc]
  rw [inputEq] at extendedBody
  have reentryEq : decClock { targetBody with clock := targetBody.clock + recursiveClock } =
      { decClock targetBody with clock := (decClock targetBody).clock + recursiveClock } := by
    simp only [decClock]
    congr 1
    omega
  have bodyDecrease := StackSemEvaluateClock.evaluateClock body source bodyResult bodyPost bodyExecution
  have recursiveDecrease := StackSemEvaluateClock.evaluateClock (.loop body) (decClock bodyPost) result post execution
  refine ⟨clock + recursiveClock, targetPost, finalSpace, by
    simp only [decClock] at recursiveBudget recursiveDecrease
    omega, postRelation, ?_, guard⟩
  rw [comp, evaluateLoopUnclamped, extendedBody]
  simp only [continuing, if_true]
  rw [if_neg (show targetBody.clock + recursiveClock ≠ 0 by omega), reentryEq]
  exact targetExecution

/-- Genuine recursive Loop case. The original three premises are retained;
only the body IH at the fixed source and actual guarded body-post reentry IH
are added. Both original compTop/comp existential conclusions remain intact.
The full native evaluator inherits its documented real-carrier assurance limit;
this proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectLoop {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : BoundedProgramIH C F body source)
    (reentryIH : BoundedLoopReentryIH C F body source)
    (hypothesis : StackSemEvaluate.evaluate (.loop body, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - post.clock) (compTop info (.loop body)) info target post result ∧
    BoundedSimulation 0 (source.clock - post.clock) (comp info (.loop body)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have bodyNonerror := loopBodyNonError body source post result execution nonerror
  have same : compTop info (.loop body) = comp info (.loop body) := rfl
  rw [same]
  suffices simulation : BoundedSimulation 0 (source.clock - post.clock) (comp info (.loop body)) info target post result by
    exact ⟨simulation, simulation⟩
  rw [evaluateLoopUnclamped] at execution
  rcases bodyExecution : StackSemEvaluate.evaluate (body, source) with ⟨bodyResult, bodyPost⟩
  rw [bodyExecution] at execution bodyNonerror
  change bodyResult ≠ some .error at bodyNonerror
  by_cases continuing : contLoop bodyResult = true
  · simp only [continuing, if_true] at execution
    by_cases zero : bodyPost.clock = 0
    · rw [if_pos zero] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact compCorrectLoopTimeout body info source target bodyPost bodyResult bodyIH
        bodyExecution bodyNonerror relation continuing zero
    · rw [if_neg zero] at execution
      exact compCorrectLoopReentry body info source target bodyPost post bodyResult result
        bodyIH reentryIH bodyExecution bodyNonerror relation continuing zero execution nonerror
  · have exit : contLoop bodyResult = false := by
      cases h : contLoop bodyResult <;> simp_all
    simp only [exit, Bool.false_eq_true, if_false] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    exact compCorrectLoopExit body info source target bodyPost bodyResult bodyIH
      bodyExecution bodyNonerror relation exit


end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.compCorrectLoop
