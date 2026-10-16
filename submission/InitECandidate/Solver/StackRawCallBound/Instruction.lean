import InitECandidate.Solver.StackRawCallBound.Common

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall

theorem evaluateCompInst {width : Nat} [NeZero width] {C F : Type}
    (instruction : Compiler.Encoders.Asm.HolInst width) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    ∃ clock targetState stackSpace,
      clock + 0 ≤ source.clock - resultState.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate
        (comp info (.inst instruction), { target with clock := clock + target.clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rw [StackSemEvaluate.evaluate_inst] at execution
  cases primitive : StackSemInst.instHOL instruction source with
  | none => simp [primitive] at execution; obtain ⟨rfl, _⟩ := execution; exact (nonerror rfl).elim
  | some state =>
    simp only [primitive, Prod.mk.injEq] at execution
    obtain ⟨rfl, rfl⟩ := execution
    obtain ⟨targetState, postRelation, targetExecution⟩ :=
      instHOL_stateRel instruction info source target state relation primitive
    refine ⟨0, targetState, targetState.stackSpace, Nat.zero_le _, postRelation, ?_, fun _ => rfl⟩
    have clockSelf : { target with clock := 0 + target.clock } = target := by
      cases target
      simp
    have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
      cases targetState
      rfl
    rw [clockSelf, stackSelf]
    simp only [comp, StackSemEvaluate.evaluate_inst, targetExecution]

end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.evaluateCompInst
