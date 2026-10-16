import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Seq

/-! Sequential Stack removal keeps the result-dependent bound: a first run
that continues has zero extra clock, while a halt never executes the second. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang StackSemEvaluate StackSemControl
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.Seq

theorem compCorrectSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (firstIH : ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
      (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound first k →
      ∃ clock postTarget, clock ≤ resultBudget r ∧
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (secondIH : ∀ (middle : StackSemStateFiniteExact width C F),
      evaluate (first, source) = (none, middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k middle t ∧ StackProps.regBound second k →
      ∃ clock postTarget, clock ≤ resultBudget r ∧
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.seq first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.seq first second) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer (.seq first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change StackProps.regBound first pointer ∧ StackProps.regBound second pointer at lower
  rcases firstRun : evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
    rw [evaluateSeqNone first second source middle firstRun] at sourceRun
    obtain ⟨firstClock, middleTarget, firstBound, firstTargetRun, middleRelation⟩ :=
      firstIH none middle target pointer bounds jump ⟨firstRun, by simp, relation, lower.1⟩
    change stateRelHOL jump bounds pointer middle middleTarget at middleRelation
    obtain ⟨secondClock, postTarget, secondBound, secondTargetRun, postRelation⟩ :=
      secondIH middle firstRun result postSource middleTarget pointer bounds jump
        ⟨sourceRun, notError, middleRelation, lower.2⟩
    have extraRun := StackProps.evaluateAddClock secondClock
      (comp jump bounds pointer first) {target with clock := firstClock + target.clock}
      none middleTarget ⟨firstTargetRun, by simp⟩
    have combinedRun :
        evaluate (comp jump bounds pointer first,
          {target with clock := (firstClock + secondClock) + target.clock}) =
          (none, {middleTarget with clock := secondClock + middleTarget.clock}) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extraRun
    have zero : firstClock = 0 := by simpa only [resultBudget, Nat.le_zero] using firstBound
    refine ⟨firstClock + secondClock, postTarget, (by omega), ?_, ?_⟩
    · rw [comp, evaluateSeqNone _ _ _ _ combinedRun]
      exact secondTargetRun
    · cases result with
      | none => exact postRelation
      | some value => cases value <;> exact postRelation
  | some firstResult =>
    rw [evaluateSeqSome first second source middle firstResult firstRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨clock, postTarget, small, targetRun, postRelation⟩ :=
      firstIH (some firstResult) middle target pointer bounds jump
        ⟨firstRun, notError, relation, lower.1⟩
    refine ⟨clock, postTarget, small, ?_, ?_⟩
    · rw [comp, evaluateSeqSome _ _ _ _ _ targetRun]
    · cases firstResult <;> exact postRelation
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectSeq
