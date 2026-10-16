import InitECandidate.Solver.StackRemoveBound.Allocation
import InitECandidate.Solver.StackRemoveBound.Free
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackSpace

/-! Constructor contracts for recursive Stack-removal accounting. Only a halt
may need an extra clock, so a continuing first sub-run cannot accumulate one. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

def resultBudget {width : Nat} [NeZero width] (result : Option (StackSemResult width)) : Nat :=
  match result with
  | some (.halt _) => 1
  | _ => 0

theorem compCorrectStackFree {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackFree count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackFree count : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  obtain ⟨clock, postTarget, zero, targetRun, postRelation⟩ :=
    evaluateStackFree jump bounds pointer count source target postSource result
      ⟨sourceRun, notError, relation⟩
  refine ⟨clock, postTarget, by rw [zero]; exact Nat.zero_le _, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => exact postRelation
    | some result =>
      cases result <;> first | exact postRelation | exact postRelation.2.2.2.2.2.2.2.2.2.1

theorem compCorrectStackAlloc {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackAlloc count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackAlloc count : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  obtain ⟨clock, postTarget, small, zero, targetRun, postRelation⟩ :=
    evaluateStackAlloc jump bounds pointer count source target postSource result
      ⟨sourceRun, notError, relation⟩
  have bound : clock ≤ resultBudget result := by
    by_cases overflow : source.stackSpace < count
    · rw [StackSemEvaluate.evaluate_stackAlloc] at sourceRun
      simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false, if_pos overflow] at sourceRun
      have resultEq := (Prod.mk.inj sourceRun).1
      rw [← resultEq]
      exact small
    · rw [zero (Nat.le_of_not_gt overflow)]
      exact Nat.zero_le _
  refine ⟨clock, postTarget, bound, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => simpa using postRelation
    | some result =>
      cases result <;> simp at postRelation <;>
        first | exact postRelation | exact postRelation.2.2.2.2.2.2.2.2.2.1

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectStackFree
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectStackAlloc
