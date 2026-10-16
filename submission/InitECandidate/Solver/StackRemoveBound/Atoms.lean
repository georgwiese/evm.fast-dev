import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Atoms

/-! Expose zero extra clocks in the original guarded Stack-removal case proofs. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

theorem compCorrectSkip {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.skip : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer .skip,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  rw [StackSemEvaluate.evaluate_skip] at sourceRun
  rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  refine ⟨0, target, Nat.zero_le _, ?_, relation⟩
  simp [comp, StackSemEvaluate.evaluate_skip]

/-- Full original Halt case with its unchanged existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectHalt {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.halt register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.halt register) : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.halt register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have registerBound : register < pointer := bound
  have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, registerBound⟩
  rw [StackSemEvaluate.evaluate_halt] at sourceRun
  cases sourceLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [sourceLookup] at sourceRun
    have resultEq := (Prod.mk.inj sourceRun).1
    exact (notError resultEq.symm).elim
  | some value =>
    rw [sourceLookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have targetLookup : StackSemStateOps.getVar register target = some value :=
      lookupEq.symm.trans sourceLookup
    refine ⟨0, StackSemStateOps.emptyEnv target, Nat.zero_le _, ?_, ?_⟩
    · simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_halt register target).trans
          (by rw [targetLookup])
    · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1

/-- Full original Alloc case with its unchanged existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectAlloc {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.alloc register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.alloc register) : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.alloc register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  have noAlloc := relation
  simp only [stateRelHOL] at noAlloc
  have flag := noAlloc.2.2.2.2.2.1
  rw [StackSemEvaluate.evaluate_alloc] at sourceRun
  simp only [flag, Bool.not_false, ite_true] at sourceRun
  have resultEq := (Prod.mk.inj sourceRun).1
  exact (notError resultEq.symm).elim

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectSkip
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectHalt
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectAlloc
