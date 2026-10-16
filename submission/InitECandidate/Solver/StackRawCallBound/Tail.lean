import InitECandidate.Solver.StackRawCallBound.Common
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Tail

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack.Compiler.Backend.StackRawCall.RawCallCase

abbrev BoundedTailCalleeIH {width : Nat} [NeZero width] (C F : Type)
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) : Prop :=
  handler = none → ∀ program, findCode dest source.regs source.code = some program →
    source.clock ≠ 0 →
    ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
      (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, decClock source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info (decClock source) target →
    BoundedSimulation 0 ((decClock source).clock - post.clock) (compTop info program) info target post result

theorem compCorrectCallTail {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : BoundedTailCalleeIH C F dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation (callCredit (.call none dest handler) source.clock) (source.clock - post.clock) (compTop info (.call none dest handler)) info target post result ∧
    BoundedSimulation (callCredit (.call none dest handler) source.clock) (source.clock - post.clock) (comp info (.call none dest handler)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change BoundedSimulation (callCredit (.call none dest handler) source.clock) (source.clock - post.clock) (.call none dest handler) info target post result ∧
    BoundedSimulation (callCredit (.call none dest handler) source.clock) (source.clock - post.clock) (.call none dest handler) info target post result
  suffices simulation : BoundedSimulation (callCredit (.call none dest handler) source.clock) (source.clock - post.clock) (.call none dest handler) info target post result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_call] at execution
  cases lookup : findCode dest source.regs source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      cases handler with
      | some handler =>
          simp only [Prod.mk.injEq] at execution
          exact False.elim (nonerror execution.1.symm)
      | none =>
          obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
            callEntry info source target relation dest program lookup
          have clockEq := LoopCase.stateRel_clock info source target relation
          by_cases zero : source.clock = 0
          · simp only [zero, if_true, Prod.mk.injEq] at execution
            obtain ⟨rfl, rfl⟩ := execution
            refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace, by simp [callCredit, zero],
              LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_⟩
            · have targetZero : target.clock = 0 := clockEq.trans zero
              simp only [Nat.add_zero, StackSemEvaluate.evaluate_call, targetLookup,
                targetZero, if_true]
              have update : {target with clock := 0} = target := by rw [← targetZero]
              rw [update]
            · simp
          · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
            rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
              ⟨bodyResult, bodyPost⟩
            rw [bodyExecution] at execution
            by_cases bad : badFunReturn bodyResult = true
            · simp only [bad, if_true, Prod.mk.injEq] at execution
              exact False.elim (nonerror execution.1.symm)
            · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
              obtain ⟨rfl, rfl⟩ := execution
              obtain ⟨clock, targetPost, space, budget, postRelation, targetExecution, guard⟩ :=
                calleeIH rfl program lookup zero entryInfo (decClock target) bodyPost bodyResult
                  ⟨bodyExecution, nonerror,
                    LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
              have frames : stateOk info source.code := by
                obtain ⟨_, _, _, frames, _⟩ := relation
                exact frames
              have postFrames := stateOk_afterEvaluate info program (decClock source)
                bodyPost bodyResult frames bodyExecution
              have decrease := StackSemEvaluateClock.evaluateClock program (decClock source) bodyResult bodyPost bodyExecution
              refine ⟨clock, targetPost, space, by
                simp only [callCredit, zero, if_false]
                simp only [decClock] at budget decrease
                omega,
                stateRel_changeInfo entryInfo info bodyPost targetPost postRelation postFrames,
                ?_, guard⟩
              have targetNonzero : target.clock ≠ 0 := by omega
              have addedNonzero : target.clock + clock ≠ 0 := by omega
              rw [StackSemEvaluate.evaluate_call]
              simp only [targetLookup, addedNonzero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              simp only [Flapjack.Compiler.Backend.StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
                targetExecution, bad, Bool.false_eq_true, if_false]


end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.compCorrectCallTail
