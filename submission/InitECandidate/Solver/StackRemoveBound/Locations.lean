import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Locations

/-! Expose zero extra clocks in the original guarded Stack-removal case proofs. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.Locations
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

theorem compCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (register first second : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate ((.locValue register first second), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.locValue register first second) : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.locValue register first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  rw [StackSemEvaluate.evaluate_locValue] at sourceRun
  by_cases checked : StackSem.locCheckExact source.code (first, second)
  · rw [if_pos checked] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have codeRelation : codeRelHOL jump bounds pointer source.code target.code :=
      relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have targetChecked := LabelPreservation.codeRelLocCheck jump bounds pointer
      source.code target.code first second ⟨codeRelation, checked⟩
    have registerBound : register < pointer := bound
    refine ⟨0, StackSemStateOps.setVar register (.loc first second) target, Nat.zero_le _, ?_, ?_⟩
    · simp [comp, StackSemEvaluate.evaluate_locValue, targetChecked]
    · exact StateUpdates.stateRelSetVar jump bounds pointer register (.loc first second)
        source target ⟨relation, registerBound⟩
  · rw [if_neg checked] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectLocValue
