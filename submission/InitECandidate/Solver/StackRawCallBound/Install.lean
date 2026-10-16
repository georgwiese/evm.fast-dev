import InitECandidate.Solver.StackRawCallBound.Common
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Install

namespace InitECandidate.Solver.StackRawCallBound.InstallCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.InstallCase

-- Strengthen the pinned constructive proofs by retaining their zero witnesses
-- and adding the numerical bound to each actual simulation conclusion.
theorem compCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - post.clock) (compTop info (.install ptr len dptr dlen ret)) info target post result ∧
    BoundedSimulation 0 (source.clock - post.clock) (comp info (.install ptr len dptr dlen ret)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  obtain ⟨targetPost, postRelation, targetExecution⟩ :=
    evaluateInstall_stateRel ptr len dptr dlen ret info source target post result
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

end InitECandidate.Solver.StackRawCallBound.InstallCase
#print axioms InitECandidate.Solver.StackRawCallBound.InstallCase.compCorrectInstall
