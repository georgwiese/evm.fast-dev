import InitECandidate.Solver.StackRawCallBound.Common
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.MemoryFfi

namespace InitECandidate.Solver.StackRawCallBound.MemoryFfiCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.MemoryFfiCase

-- Strengthen the pinned constructive proofs by retaining their zero witnesses
-- and adding the numerical bound to each actual simulation conclusion.
theorem compCorrectMemory {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : MemoryLeaf program) (info : Spt Nat)
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






theorem compCorrectShMemOp {width : Nat} [NeZero width] {C F : Type}
    (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec width) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.shMemOp op r (.addr a w), source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.shMemOp op r (.addr a w))) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.shMemOp op r (.addr a w))) info target resultState result :=
  compCorrectMemory (.shMemOp op r (.addr a w)) (.shMemOp op r a w)
    info source target resultState result hypothesis


theorem compCorrectCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.codeBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.codeBufferWrite r1 r2)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.codeBufferWrite r1 r2)) info target resultState result :=
  compCorrectMemory (.codeBufferWrite r1 r2) (.codeBufferWrite r1 r2)
    info source target resultState result hypothesis


theorem compCorrectDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.dataBufferWrite r1 r2)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.dataBufferWrite r1 r2)) info target resultState result :=
  compCorrectMemory (.dataBufferWrite r1 r2) (.dataBufferWrite r1 r2)
    info source target resultState result hypothesis


theorem compCorrectFfi {width : Nat} [NeZero width] {C F : Type}
    (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.ffi function ptr len ptr2 len2 ret, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.ffi function ptr len ptr2 len2 ret)) info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.ffi function ptr len ptr2 len2 ret)) info target resultState result :=
  compCorrectMemory (.ffi function ptr len ptr2 len2 ret) (.ffi function ptr len ptr2 len2 ret)
    info source target resultState result hypothesis
end InitECandidate.Solver.StackRawCallBound.MemoryFfiCase
#print axioms InitECandidate.Solver.StackRawCallBound.MemoryFfiCase.compCorrectMemory
#print axioms InitECandidate.Solver.StackRawCallBound.MemoryFfiCase.compCorrectShMemOp
#print axioms InitECandidate.Solver.StackRawCallBound.MemoryFfiCase.compCorrectCodeBufferWrite
#print axioms InitECandidate.Solver.StackRawCallBound.MemoryFfiCase.compCorrectDataBufferWrite
#print axioms InitECandidate.Solver.StackRawCallBound.MemoryFfiCase.compCorrectFfi
