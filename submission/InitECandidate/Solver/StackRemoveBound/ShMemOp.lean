import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.ShMemOp

/-! Expose zero extra clocks in the original guarded Stack-removal case proofs. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.ShMemOp
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps StackSemShMem

theorem compCorrectShMemOp {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (register base : Nat) (offset : BitVec width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.shMemOp op register (.addr base offset), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.shMemOp op register (.addr base offset) : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer (.shMemOp op register (.addr base offset)),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change register < pointer ∧ base < pointer at bound
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_shMemOp] at sourceRun
  cases addressRun : StackSemExpressions.wordExp source (.op .add [.var base, .const offset]) with
  | none =>
    simp only [addressRun] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some address =>
    have targetAddress := ExpressionSimulation.stateRelWordExp jump bounds pointer source target
      (.op .add [.var base, .const offset]) address
      ⟨relation, by simpa [StackProps.regBoundExp] using bound.2, addressRun⟩
    simp only [addressRun] at sourceRun
    by_cases zero : source.clock = 0
    · simp only [zero, ite_true] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
      subst result
      subst postSource
      refine ⟨0, emptyEnv target, Nat.zero_le _, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluate_shMemOp op register base offset target).trans
            (by simp only [targetAddress, clocks, zero, ite_true])
      · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
    · simp only [zero, ite_false] at sourceRun
      obtain ⟨postTarget, targetRun, postRelation⟩ := shMemOpSimulation jump bounds pointer register
        op address (decClock source) (decClock target) postSource result
        (RelationLaws.stateRelDecClock jump bounds pointer source target relation)
        bound.1 sourceRun notError
      refine ⟨0, postTarget, Nat.zero_le _, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluate_shMemOp op register base offset target).trans
            (by simp only [targetAddress, clocks, zero, ite_false]; exact targetRun)
      · cases result with
        | none => exact postRelation
        | some outcome => cases outcome <;> exact postRelation

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectShMemOp
