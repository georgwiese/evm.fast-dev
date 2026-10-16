import InitECandidate.Solver.StackRawCallBound.Return
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Return

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack.Compiler.Backend.StackRawCall.RawCallCase

abbrev BoundedCallIH {width : Nat} [NeZero width] (C F : Type)
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) : Prop :=
  match ret with
  | none => BoundedTailCalleeIH C F dest handler source
  | some (body, link, l1, l2) =>
      BoundedReturnCalleeIH C F dest link l1 l2 source ∧
      BoundedReturnContinuationIH C F body dest link l1 l2 source ∧
      BoundedExceptionContinuationIH C F handler dest link l1 l2 source

theorem compCorrectCall {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (induction : BoundedCallIH C F ret dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call ret dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation (callCredit (.call ret dest handler) source.clock) (source.clock - post.clock) (compTop info (.call ret dest handler)) info target post result ∧
    BoundedSimulation (callCredit (.call ret dest handler) source.clock) (source.clock - post.clock) (comp info (.call ret dest handler)) info target post result := by
  cases ret with
  | none => exact compCorrectCallTail dest handler info source target post result induction hypothesis
  | some triple =>
      obtain ⟨body, link, l1, l2⟩ := triple
      obtain ⟨calleeIH, returnIH, exceptionIH⟩ := induction
      exact compCorrectCallReturn body link l1 l2 dest handler info source target post result
        calleeIH returnIH exceptionIH hypothesis

end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.compCorrectCall
