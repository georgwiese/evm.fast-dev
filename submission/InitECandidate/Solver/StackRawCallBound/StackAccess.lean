import InitECandidate.Solver.StackRawCallBound.Common
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.StackAccess

namespace InitECandidate.Solver.StackRawCallBound.StackAccessCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.StackAccessCase

-- Strengthen the pinned constructive proofs by retaining their zero witnesses
-- and adding the numerical bound to each actual simulation conclusion.
theorem compCorrectStack {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : StackLeaf program) (info : Spt Nat)
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



theorem compCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (register first second : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.locValue register first second, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.locValue register first second)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.locValue register first second)) info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have labels := locCheck_stateRel info source target relation (first, second)
  rw [StackSemEvaluate.evaluate_locValue] at execution
  split at execution
  · rename_i location
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    obtain ⟨code, domain, equality, frames, entries⟩ := relation
    subst target
    have postRelation : stateRel info (setVar register (.loc first second) source)
        { setVar register (.loc first second) source with code := code } := by
      exact ⟨code, domain, rfl, frames, entries⟩
    have targetLocation : StackSem.locCheckExact code (first, second) := labels.mpr location
    constructor <;>
      refine ⟨0, { setVar register (.loc first second) source with code := code },
        (setVar register (.loc first second) source).stackSpace, Nat.zero_le _, postRelation, ?_, ?_⟩
    all_goals try (intro _; rfl)
    all_goals simp only [compTop, comp, Nat.add_zero, StackSemEvaluate.evaluate_locValue,
      targetLocation, if_true, setVar]
  · exact False.elim (nonerror (Prod.mk.inj execution).1.symm)


theorem compCorrectStackAlloc {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackAlloc n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.stackAlloc n)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.stackAlloc n)) info target resultState result :=
  compCorrectStack (.stackAlloc n) (.stackAlloc n)
    info source target resultState result hypothesis


theorem compCorrectStackFree {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackFree n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.stackFree n)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.stackFree n)) info target resultState result :=
  compCorrectStack (.stackFree n) (.stackFree n)
    info source target resultState result hypothesis


theorem compCorrectStackLoad {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackLoad r n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.stackLoad r n)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.stackLoad r n)) info target resultState result :=
  compCorrectStack (.stackLoad r n) (.stackLoad r n)
    info source target resultState result hypothesis


theorem compCorrectStackLoadAny {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackLoadAny r rn, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.stackLoadAny r rn)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.stackLoadAny r rn)) info target resultState result :=
  compCorrectStack (.stackLoadAny r rn) (.stackLoadAny r rn)
    info source target resultState result hypothesis


theorem compCorrectStackStore {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackStore r n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.stackStore r n)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.stackStore r n)) info target resultState result :=
  compCorrectStack (.stackStore r n) (.stackStore r n)
    info source target resultState result hypothesis


theorem compCorrectStackStoreAny {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackStoreAny r rn, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.stackStoreAny r rn)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.stackStoreAny r rn)) info target resultState result :=
  compCorrectStack (.stackStoreAny r rn) (.stackStoreAny r rn)
    info source target resultState result hypothesis


theorem compCorrectStackGetSize {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackGetSize r, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.stackGetSize r)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.stackGetSize r)) info target resultState result :=
  compCorrectStack (.stackGetSize r) (.stackGetSize r)
    info source target resultState result hypothesis


theorem compCorrectStackSetSize {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackSetSize r, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.stackSetSize r)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.stackSetSize r)) info target resultState result :=
  compCorrectStack (.stackSetSize r) (.stackSetSize r)
    info source target resultState result hypothesis


theorem compCorrectBitmapLoad {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.bitmapLoad r v, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.bitmapLoad r v)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.bitmapLoad r v)) info target resultState result :=
  compCorrectStack (.bitmapLoad r v) (.bitmapLoad r v)
    info source target resultState result hypothesis

end InitECandidate.Solver.StackRawCallBound.StackAccessCase
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectStack
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectLocValue
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectStackAlloc
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectStackFree
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectStackLoad
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectStackLoadAny
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectStackStore
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectStackStoreAny
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectStackGetSize
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectStackSetSize
#print axioms InitECandidate.Solver.StackRawCallBound.StackAccessCase.compCorrectBitmapLoad
