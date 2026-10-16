import InitECandidate.Solver.StackRawCallBound.Common
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.AllocationStore

namespace InitECandidate.Solver.StackRawCallBound.AllocationStoreCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.AllocationStoreCase

-- Strengthen the pinned constructive proofs by retaining their zero witnesses
-- and adding the numerical bound to each actual simulation conclusion.
theorem compCorrectAlloc {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.alloc register, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - post.clock) (compTop info (.alloc register)) info target post result ∧
    BoundedSimulation 0 (source.clock - post.clock) (comp info (.alloc register)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  obtain ⟨targetPost, postRelation, targetExecution⟩ := postRelationOfTransport (fun state => StackSemEvaluate.evaluate (.alloc register, state))
      source target post info result (evaluateAlloc_codeUpdate register source) execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, targetPost, targetPost.stackSpace, Nat.zero_le _, postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution


theorem compCorrectStoreConsts {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - post.clock) (compTop info (.storeConsts first second stub)) info target post result ∧
    BoundedSimulation 0 (source.clock - post.clock) (comp info (.storeConsts first second stub)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  obtain ⟨targetPost, postRelation, targetExecution⟩ := evaluateStoreConsts_stateRel first second stub info source target post result
      execution nonerror relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, targetPost, targetPost.stackSpace, Nat.zero_le _, postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution
end InitECandidate.Solver.StackRawCallBound.AllocationStoreCase
#print axioms InitECandidate.Solver.StackRawCallBound.AllocationStoreCase.compCorrectAlloc
#print axioms InitECandidate.Solver.StackRawCallBound.AllocationStoreCase.compCorrectStoreConsts
