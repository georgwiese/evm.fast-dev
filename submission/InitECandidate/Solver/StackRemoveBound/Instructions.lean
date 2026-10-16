import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Instructions

/-! Expose zero extra clocks in the original guarded Stack-removal case proofs. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.Instructions
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

theorem compCorrectInst {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : HolInst width)
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.inst instruction) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  rw [StackSemEvaluate.evaluate_inst] at sourceRun
  cases instRun : StackSemInst.instHOL instruction source with
  | none =>
    rw [instRun] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some state =>
    rw [instRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have instructionBound : StackProps.regBoundInst instruction pointer := bound
    obtain ⟨postTarget, targetRun, postRelation⟩ :=
      InstructionSimulation.stateRelInst jump bounds pointer instruction source target state
        ⟨relation, instructionBound, instRun⟩
    refine ⟨0, postTarget, Nat.zero_le _, ?_, postRelation⟩
    simpa only [comp, Nat.zero_add] using
      (StackSemEvaluate.evaluate_inst instruction target).trans (by rw [targetRun])

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectInst
