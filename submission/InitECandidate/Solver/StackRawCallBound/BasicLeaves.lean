import InitECandidate.Solver.StackRawCallBound.Common
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.BasicLeaves

namespace InitECandidate.Solver.StackRawCallBound.BasicLeaves
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.BasicLeaves

-- Strengthen the pinned constructive proofs by retaining their zero witnesses
-- and adding the numerical bound to each actual simulation conclusion.
theorem compCorrectBasic {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : BasicLeaf program) (info : Spt Nat)
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


theorem compCorrectSkip {width : Nat} [NeZero width] {C F : Type}
     (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.skip : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.skip : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.skip : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.skip : HolProg width) .skip info source target resultState result hypothesis


theorem compCorrectHalt {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.halt register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.halt register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.halt register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.halt register : HolProg width) (.halt register) info source target resultState result hypothesis


theorem compCorrectGet {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (name : StoreName) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.get register name : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.get register name : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.get register name : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.get register name : HolProg width) (.get register name) info source target resultState result hypothesis


theorem compCorrectSet {width : Nat} [NeZero width] {C F : Type}
    (name : StoreName) (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.set name register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.set name register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.set name register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.set name register : HolProg width) (.set name register) info source target resultState result hypothesis


theorem compCorrectOpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (operator : Compiler.Encoders.Asm.HolBinop) (destination input : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.opCurrHeap operator destination input : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.opCurrHeap operator destination input : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.opCurrHeap operator destination input : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.opCurrHeap operator destination input : HolProg width) (.opCurrHeap operator destination input) info source target resultState result hypothesis


theorem compCorrectTick {width : Nat} [NeZero width] {C F : Type}
     (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.tick : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.tick : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.tick : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasic (.tick : HolProg width) .tick info source target resultState result hypothesis

end InitECandidate.Solver.StackRawCallBound.BasicLeaves
#print axioms InitECandidate.Solver.StackRawCallBound.BasicLeaves.compCorrectBasic
#print axioms InitECandidate.Solver.StackRawCallBound.BasicLeaves.compCorrectSkip
#print axioms InitECandidate.Solver.StackRawCallBound.BasicLeaves.compCorrectHalt
#print axioms InitECandidate.Solver.StackRawCallBound.BasicLeaves.compCorrectGet
#print axioms InitECandidate.Solver.StackRawCallBound.BasicLeaves.compCorrectSet
#print axioms InitECandidate.Solver.StackRawCallBound.BasicLeaves.compCorrectOpCurrHeap
#print axioms InitECandidate.Solver.StackRawCallBound.BasicLeaves.compCorrectTick
