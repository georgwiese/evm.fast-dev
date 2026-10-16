import InitECandidate.Solver.StackRawCallBound.Common
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.ControlLeaves

namespace InitECandidate.Solver.StackRawCallBound.ControlLeaves
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.ControlLeaves

-- Strengthen the pinned constructive proofs by retaining their zero witnesses
-- and adding the numerical bound to each actual simulation conclusion.
theorem compCorrectControl {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : ControlLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  obtain ⟨execution, _, relation⟩ := hypothesis
  obtain ⟨targetState, postRelation, targetExecution⟩ :=
    evaluate_stateRel program leaf info source target resultState result execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  have compSelf : comp info program = program := by
    cases leaf <;> rfl
  have compTopSelf : compTop info program = program := by
    cases leaf <;> rfl
  constructor <;>
    refine ⟨0, targetState, targetState.stackSpace, Nat.zero_le _, postRelation, ?_, fun _ => rfl⟩
  · rw [clockSelf, stackSelf, compTopSelf]
    exact targetExecution
  · rw [clockSelf, stackSelf, compSelf]
    exact targetExecution


theorem compCorrectReturn {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.ret register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.ret register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.ret register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectControl (.ret register : HolProg width) (.ret register) info source target resultState result hypothesis


theorem compCorrectRaise {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.raise register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.raise register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.raise register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectControl (.raise register : HolProg width) (.raise register) info source target resultState result hypothesis


theorem compCorrectBreak {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.break register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.break register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.break register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectControl (.break register : HolProg width) (.break register) info source target resultState result hypothesis


theorem compCorrectContinue {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.continue register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.continue register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.continue register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectControl (.continue register : HolProg width) (.continue register) info source target resultState result hypothesis

end InitECandidate.Solver.StackRawCallBound.ControlLeaves
#print axioms InitECandidate.Solver.StackRawCallBound.ControlLeaves.compCorrectControl
#print axioms InitECandidate.Solver.StackRawCallBound.ControlLeaves.compCorrectReturn
#print axioms InitECandidate.Solver.StackRawCallBound.ControlLeaves.compCorrectRaise
#print axioms InitECandidate.Solver.StackRawCallBound.ControlLeaves.compCorrectBreak
#print axioms InitECandidate.Solver.StackRawCallBound.ControlLeaves.compCorrectContinue
