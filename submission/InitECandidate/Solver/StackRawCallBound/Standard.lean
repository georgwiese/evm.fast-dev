import InitECandidate.Solver.StackRawCallBound.Common

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.SeqCase

theorem simulateStandardSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : BoundedProgramIH C F first source)
    (secondIH : BoundedSeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - post.clock) (.seq (comp info first) (comp info second)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
      rw [evaluateSeqUnclamped, firstRun] at execution
      obtain ⟨firstClock, targetMiddle, firstSpace, firstBudget, middleRelation, firstTargetRun, firstGuard⟩ :=
        firstIH info target middle none ⟨firstRun, by simp, relation⟩
      have spaceEq := firstGuard (by simp)
      subst firstSpace
      have spaceSelf : { targetMiddle with stackSpace := targetMiddle.stackSpace } =
          targetMiddle := by cases targetMiddle; rfl
      rw [spaceSelf] at firstTargetRun
      obtain ⟨secondClock, targetPost, finalSpace, secondBudget, postRelation, secondTargetRun, finalGuard⟩ :=
        secondIH middle firstRun info targetMiddle post result
          ⟨execution, nonerror, middleRelation⟩
      have extendedFirst := Compiler.Backend.StackProps.evaluateAddClock secondClock
        (comp info first) { target with clock := target.clock + firstClock }
        none targetMiddle ⟨firstTargetRun, by simp⟩
      have inputEq : { { target with clock := target.clock + firstClock } with
          clock := ({ target with clock := target.clock + firstClock }).clock + secondClock } =
          { target with clock := target.clock + (firstClock + secondClock) } := by
        simp only [Nat.add_assoc]
      rw [inputEq] at extendedFirst
      have firstDecrease := StackSemEvaluateClock.evaluateClock first source none middle firstRun
      have secondDecrease := StackSemEvaluateClock.evaluateClock second middle result post execution
      refine ⟨firstClock + secondClock, targetPost, finalSpace, by omega, postRelation, ?_, finalGuard⟩
      rw [evaluateSeqUnclamped, extendedFirst]
      exact secondTargetRun
  | some firstResult =>
      rw [evaluateSeqUnclamped, firstRun] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      obtain ⟨clock, targetPost, finalSpace, secondBudget, postRelation, targetRun, guard⟩ :=
        firstIH info target middle (some firstResult) ⟨firstRun, nonerror, relation⟩
      refine ⟨clock, targetPost, finalSpace, by omega, postRelation, ?_, guard⟩
      rw [evaluateSeqUnclamped, targetRun]


end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.simulateStandardSeq
