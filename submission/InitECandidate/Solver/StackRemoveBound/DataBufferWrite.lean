import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.DataBufferWrite

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.DataBufferWrite
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

theorem compCorrectDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (first second : Nat)
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.dataBufferWrite first second : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.dataBufferWrite first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStack := relation.1
  rw [StackSemEvaluate.evaluate_dataBufferWrite] at sourceRun
  simp only [useStack, not_true_eq_false, ite_false] at sourceRun
  cases firstLookup : StackSemStateOps.getVar first source with
  | none =>
    simp only [firstLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some firstValue =>
    cases firstValue with
    | loc block offset =>
      simp only [firstLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | word address =>
      cases secondLookup : StackSemStateOps.getVar second source with
      | none =>
        simp only [firstLookup, secondLookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | some secondValue =>
        cases secondValue with
        | loc block offset =>
          simp only [firstLookup, secondLookup] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
        | word value =>
          simp only [firstLookup, secondLookup] at sourceRun
          cases written : wordSemBufferWrite source.dataBuffer address value with
          | none =>
            rw [written] at sourceRun
            exact (notError (Prod.mk.inj sourceRun).1.symm).elim
          | some updated =>
            rw [written] at sourceRun
            rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
            subst result
            subst postSource
            refine ⟨0, {target with memory := fun key => if key = address then .word value else target.memory key}, Nat.zero_le _, ?_, ?_⟩
            · simpa only [comp, Nat.zero_add] using
                bufferWriteTargetExecution jump bounds pointer first second source target address value updated
                  relation bound.1 bound.2 firstLookup secondLookup written
            · simpa only [useStack] using bufferWriteStateRel jump bounds pointer source target address value updated relation written

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectDataBufferWrite
