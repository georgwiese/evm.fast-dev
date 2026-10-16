import InitECandidate.Solver.StackRawCallBound.Common
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.JumpLower

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.JumpLowerCase
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.RawCallCase

abbrev BoundedTopProgramIH {width : Nat} [NeZero width] (C F : Type) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)),
    StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target →
    BoundedSimulation 0 (source.clock - post.clock) (compTop info program) info target post result

/-- Actual selected-callee evaluate_ind hypothesis at the fixed decClock
source. Operand reads, the unsigned comparison, code lookup and nonzero clock
are precisely the guards of the original recursive call. -/
abbrev BoundedJumpIH {width : Nat} [NeZero width] (C F : Type) (r1 r2 dest : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (left right : BitVec width) (program : HolProg width),
    StackSemStateOps.getVar r1 source = some (.word left) →
    StackSemStateOps.getVar r2 source = some (.word right) →
    Compiler.Encoders.Asm.wordCmpHOL .lower left right = true →
    sptLookup dest source.code = some program →
    source.clock ≠ 0 → BoundedTopProgramIH C F program (decClock source)

theorem compCorrectJumpLower {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : BoundedJumpIH C F r1 r2 dest source)
    (hypothesis : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - post.clock) (compTop info (.jumpLower r1 r2 dest)) info target post result ∧
    BoundedSimulation 0 (source.clock - post.clock) (comp info (.jumpLower r1 r2 dest)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change BoundedSimulation 0 (source.clock - post.clock) (.jumpLower r1 r2 dest) info target post result ∧
    BoundedSimulation 0 (source.clock - post.clock) (.jumpLower r1 r2 dest) info target post result
  suffices simulation : BoundedSimulation 0 (source.clock - post.clock) (.jumpLower r1 r2 dest) info target post result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_jumpLower] at execution
  split at execution
  · rename_i left right firstRead secondRead
    split at execution
    · rename_i lower
      simp only [findCode] at execution
      cases lookup : sptLookup dest source.code with
      | none =>
        simp only [lookup, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      | some program =>
        rw [lookup] at execution
        obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
          calleeEntry info source target relation dest program lookup
        have clockEq := LoopCase.stateRel_clock info source target relation
        by_cases zero : source.clock = 0
        · simp only [zero, if_true, Prod.mk.injEq] at execution
          obtain ⟨rfl, rfl⟩ := execution
          refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace, Nat.zero_le _,
            LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_⟩
          · simp only [Nat.add_zero, StackSemEvaluate.evaluate_jumpLower,
              getVar_targetClock info source target relation, firstRead, secondRead,
              lower, if_true, findCode, targetLookup]
            have tz : target.clock = 0 := clockEq.trans zero
            simp only [tz, if_true]
            have update : { target with clock := 0 } = target := by rw [← tz]
            rw [update]
          · simp
        · simp only [zero, if_false] at execution
          rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
            ⟨bodyResult, bodyPost⟩
          rw [bodyExecution] at execution
          by_cases bad : badFunReturn bodyResult = true
          · simp only [bad, if_true, Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
          · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
            obtain ⟨rfl, rfl⟩ := execution
            obtain ⟨clock, targetState, stackSpace, budget, postRelation, targetExecution, guard⟩ :=
              calleeIH left right program firstRead secondRead lower lookup zero
                entryInfo (decClock target) bodyPost bodyResult
                ⟨bodyExecution, nonerror,
                  LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
            have frames : stateOk info source.code := by
              obtain ⟨_, _, _, frames, _⟩ := relation
              exact frames
            have postFrames := stateOk_afterEvaluate info program (decClock source) bodyPost
              bodyResult frames bodyExecution
            refine ⟨clock, targetState, stackSpace, by
              simp only [decClock] at budget
              omega,
              stateRel_changeInfo entryInfo info bodyPost targetState postRelation postFrames,
              ?_, guard⟩
            have targetNonzero : target.clock ≠ 0 := by omega
            have addedNonzero : target.clock + clock ≠ 0 := by omega
            simp only [StackSemEvaluate.evaluate_jumpLower,
              getVar_targetClock info source target relation, firstRead, secondRead,
              lower, if_true, findCode, targetLookup, addedNonzero, if_false,
              Flapjack.Compiler.Backend.StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
              targetExecution, bad, Bool.false_eq_true, if_false]
    · rename_i notLower
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      refine ⟨0, target, target.stackSpace, Nat.zero_le _, relation, ?_, fun _ => rfl⟩
      simp only [StackSemEvaluate.evaluate_jumpLower,
        getVar_targetClock info source target relation, firstRead, secondRead,
        notLower, Bool.false_eq_true, if_false]
      have update : { target with clock := target.clock + 0 } = target := by
        cases target
        simp
      rw [update]
  · exact False.elim (nonerror (Prod.mk.inj execution).1.symm)

end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.compCorrectJumpLower
