import InitECandidate.Solver.StackRawCallBound.Common

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase

abbrev BoundedBranchIH {width : Nat} [NeZero width] (C F : Type)
    (comparison : Cmp) (register : Nat) (operand : Compiler.Encoders.Asm.HolRegImm width)
    (truth : Bool) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (left right : WordLocW width),
    StackSemStateOps.getVar register source = some left →
    StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand)
      source = some right →
    wordSemWordCmp comparison left right = some truth →
    BoundedProgramIH C F program source

theorem compCorrectIf {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : Compiler.Encoders.Asm.HolRegImm width)
    (first second : HolProg width)
    (info : Spt Nat) (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : BoundedBranchIH C F comparison register operand true first source)
    (secondIH : BoundedBranchIH C F comparison register operand false second source)
    (hypothesis : StackSemEvaluate.evaluate (.ite comparison register operand first second, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - resultState.clock) (compTop info (.ite comparison register operand first second))
      info target resultState result ∧
    BoundedSimulation 0 (source.clock - resultState.clock) (comp info (.ite comparison register operand first second))
      info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have same : compTop info (.ite comparison register operand first second) =
      comp info (.ite comparison register operand first second) := rfl
  rw [same]
  suffices simulation : BoundedSimulation 0 (source.clock - resultState.clock)
      (comp info (.ite comparison register operand first second)) info target resultState result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_ite] at execution
  split at execution
  · rename_i left right leftRead rightRead
    split at execution
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, budget, postRelation, targetExecution, guard⟩ :=
        firstIH left right leftRead rightRead compared
          info target resultState result ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, by omega, postRelation, ?_, guard⟩
      rw [evaluateCompiledIf info source target relation]
      simp_all
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, budget, postRelation, targetExecution, guard⟩ :=
        secondIH left right leftRead rightRead compared
          info target resultState result ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, by omega, postRelation, ?_, guard⟩
      rw [evaluateCompiledIf info source target relation]
      simp_all
    · simp_all
  · simp_all


end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.compCorrectIf
