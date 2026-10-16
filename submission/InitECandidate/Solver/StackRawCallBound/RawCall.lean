import InitECandidate.Solver.StackRawCallBound.Common
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Tail

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack.Compiler.Backend.StackRawCall.RawCallCase

abbrev BoundedRawCalleeIH {width : Nat} [NeZero width] (C F : Type) (dest : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ first body, sptLookup dest source.code = some (.seq first body) →
    source.clock ≠ 0 → BoundedProgramIH C F body (decClock source)

theorem compCorrectRawCall {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : BoundedRawCalleeIH C F dest source)
    (hypothesis : StackSemEvaluate.evaluate (.rawCall dest, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation (callCredit (width := width) (.rawCall dest) source.clock) (source.clock - resultState.clock) (compTop info (.rawCall dest)) info target resultState result ∧
    BoundedSimulation (callCredit (width := width) (.rawCall dest) source.clock) (source.clock - resultState.clock) (comp info (.rawCall dest)) info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change BoundedSimulation (callCredit (width := width) (.rawCall dest) source.clock) (source.clock - resultState.clock) (.rawCall dest) info target resultState result ∧
    BoundedSimulation (callCredit (width := width) (.rawCall dest) source.clock) (source.clock - resultState.clock) (.rawCall dest) info target resultState result
  suffices simulation : BoundedSimulation (callCredit (width := width) (.rawCall dest) source.clock) (source.clock - resultState.clock) (.rawCall dest) info target resultState result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_rawCall] at execution
  cases lookup : sptLookup dest source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
    rw [lookup] at execution
    cases program <;> simp only [destSeq] at execution
    all_goals try (exact False.elim (nonerror (Prod.mk.inj execution).1.symm))
    rename_i first body
    obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
      rawCallEntry info source target relation dest first body lookup
    have clockEq := LoopCase.stateRel_clock info source target relation
    by_cases zero : source.clock = 0
    · simp only [zero, if_true, Prod.mk.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace, by simp [callCredit, zero],
        LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_⟩
      · simp only [Nat.add_zero, StackSemEvaluate.evaluate_rawCall, targetLookup,
          destSeq]
        have tz : target.clock = 0 := clockEq.trans zero
        simp only [tz, if_true]
        have update : { target with clock := 0 } = target := by
          rw [← tz]
        rw [update]
      · simp
    · simp only [zero, if_false] at execution
      rcases bodyExecution : StackSemEvaluate.evaluate (body, decClock source) with
        ⟨bodyResult, bodyPost⟩
      rw [bodyExecution] at execution
      by_cases bad : badFunReturn bodyResult = true
      · simp only [bad, if_true, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨clock, targetState, stackSpace, budget, postRelation, targetExecution, guard⟩ :=
          calleeIH first body lookup zero entryInfo (decClock target) bodyPost bodyResult
            ⟨bodyExecution, nonerror,
              LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
        have frames : stateOk info source.code := by
          obtain ⟨_, _, _, frames, _⟩ := relation
          exact frames
        have postFrames := stateOk_afterEvaluate info body (decClock source) bodyPost
          bodyResult frames bodyExecution
        have decrease := StackSemEvaluateClock.evaluateClock body (decClock source) bodyResult bodyPost bodyExecution
        refine ⟨clock, targetState, stackSpace, by
          simp only [callCredit, zero, if_false]
          simp only [decClock] at budget decrease
          omega,
          stateRel_changeInfo entryInfo info bodyPost targetState postRelation postFrames,
          ?_, guard⟩
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + clock ≠ 0 := by omega
        simp only [StackSemEvaluate.evaluate_rawCall, targetLookup, destSeq,
          addedNonzero, if_false,
          Flapjack.Compiler.Backend.StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
          targetExecution, bad, Bool.false_eq_true, if_false]


end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.compCorrectRawCall
