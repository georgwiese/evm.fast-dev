import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.HeapOperation

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.HeapOperation
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

theorem compCorrectOpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (operator : BinOp) (destination input : Nat)
    (hypothesis : StackSemEvaluate.evaluate (.opCurrHeap operator destination input, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.opCurrHeap operator destination input : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.opCurrHeap operator destination input),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  have regEq : target.regs.lookup input = source.regs.lookup input :=
    relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 input bound.2
  have heapEq : target.regs.lookup (pointer + 2) = source.store.lookup .currHeap :=
    relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have expressionEq : StackSemExpressions.wordExp target (.op operator [.var input, .var (pointer + 2)]) =
      StackSemExpressions.wordExp source (.op operator [.var input, .lookup .currHeap]) := by
    simp [StackSemExpressions.wordExp, regEq, heapEq]
  rw [StackSemEvaluate.evaluate_opCurrHeap] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases valueRun : StackSemExpressions.wordExp source (.op operator [.var input, .lookup .currHeap]) with
  | none =>
    rw [valueRun] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [valueRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, StackSemStateOps.setVar destination (.word value) target, Nat.zero_le _, ?_, ?_⟩
    · have different : pointer + 2 ≠ input := by have := bound.2; omega
      simp only [comp, Nat.zero_add, StackSemEvaluate.evaluate_inst,
        StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, Option.join_some]
      simp [different, StackSemExpressions.assign, expressionEq, valueRun]
    · exact StateUpdates.stateRelSetVar jump bounds pointer destination (.word value) source target
        ⟨relation, bound.1⟩

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectOpCurrHeap
