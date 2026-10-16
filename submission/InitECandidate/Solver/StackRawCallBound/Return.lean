import InitECandidate.Solver.StackRawCallBound.Tail
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Return

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack.Compiler.Backend.StackRawCall.RawCallCase

abbrev BoundedReturnCalleeIH {width : Nat} [NeZero width] (C F : Type)
    (dest : Sum Nat Nat) (link l1 l2 : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 →
    ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
      (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (result, post) ∧ result ≠ some .error ∧
        stateRel info (decClock (setVar link (.loc l1 l2) source)) target →
      BoundedSimulation 0 ((decClock (setVar link (.loc l1 l2) source)).clock - post.clock) (compTop info program) info target post result

/-- Original return-continuation IH, guarded by the real callee lookup, clock,
evaluation and exact matching return location. Flapjack infrastructure. -/
abbrev BoundedReturnContinuationIH {width : Nat} [NeZero width] (C F : Type)
    (ret : HolProg width) (dest : Sum Nat Nat) (link l1 l2 : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 → ∀ middle,
    StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.result (.loc l1 l2)), middle) → BoundedProgramIH C F ret middle

/-- Original exception-continuation IH, retaining the actual handler and exact
matching exception location guards. Flapjack infrastructure. -/
abbrev BoundedExceptionContinuationIH {width : Nat} [NeZero width] (C F : Type)
    (handler : Option (HolProg width × Nat × Nat)) (dest : Sum Nat Nat)
    (link l1 l2 : Nat) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ program h hl1 hl2,
    findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 → handler = some (h, hl1, hl2) → ∀ middle,
    StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.exception (.loc hl1 hl2)), middle) → BoundedProgramIH C F h middle

theorem simulateReturningCallee {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (link l1 l2 : Nat) (info : Spt Nat)
    (source target middle : StackSemStateFiniteExact width C F)
    (program : HolProg width) (result : Option (StackSemResult width))
    (calleeIH : BoundedReturnCalleeIH C F dest link l1 l2 source)
    (relation : stateRel info source target)
    (lookup : findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate
      (program, decClock (setVar link (.loc l1 l2) source)) = (result, middle))
    (nonerror : result ≠ some .error) :
    ∃ entryInfo, findCode dest (target.regs.eraseEq link) target.code =
        some (compTop entryInfo program) ∧
      BoundedSimulation 1 (source.clock - middle.clock) (compTop entryInfo program) info
        (decClock (setVar link (.loc l1 l2) target)) middle result := by
  obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
    callEntryErased info source target relation dest link program lookup
  obtain ⟨clock, targetMiddle, space, budget, middleRelation, targetExecution, guard⟩ :=
    calleeIH program lookup nonzero entryInfo
      (decClock (setVar link (.loc l1 l2) target)) middle result
      ⟨execution, nonerror, LoopCase.stateRel_decClock entryInfo
        (setVar link (.loc l1 l2) source) (setVar link (.loc l1 l2) target)
        (stateRel_setVar entryInfo source target entryRelation link (.loc l1 l2))⟩
  have frames : stateOk info source.code := by
    obtain ⟨_, _, _, frames, _⟩ := relation
    exact frames
  have middleFrames := stateOk_afterEvaluate info program
    (decClock (setVar link (.loc l1 l2) source)) middle result frames execution
  have decrease := StackSemEvaluateClock.evaluateClock program
    (decClock (setVar link (.loc l1 l2) source)) result middle execution
  refine ⟨entryInfo, targetLookup, clock, targetMiddle, space, ?_,
    stateRel_changeInfo entryInfo info middle targetMiddle middleRelation middleFrames,
    targetExecution, guard⟩

  simp only [decClock, setVar] at budget decrease
  omega

theorem compCorrectCallReturn {width : Nat} [NeZero width] {C F : Type}
    (ret : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : BoundedReturnCalleeIH C F dest link l1 l2 source)
    (returnIH : BoundedReturnContinuationIH C F ret dest link l1 l2 source)
    (exceptionIH : BoundedExceptionContinuationIH C F handler dest link l1 l2 source)
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation (callCredit (.call (some (ret, link, l1, l2)) dest handler) source.clock) (source.clock - post.clock) (compTop info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result ∧
    BoundedSimulation (callCredit (.call (some (ret, link, l1, l2)) dest handler) source.clock) (source.clock - post.clock) (comp info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result := by
  classical
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  suffices simulation :
      BoundedSimulation (callCredit (.call (some (ret, link, l1, l2)) dest handler) source.clock) (source.clock - post.clock) (comp info (.call (some (ret, link, l1, l2)) dest handler))
        info target post result by
    exact ⟨by simpa only [compTop] using simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_call] at execution
  dsimp only at execution
  cases lookup : findCode dest (source.regs.eraseEq link) source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      have clockEq := LoopCase.stateRel_clock info source target relation
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨entryInfo, _, targetLookup⟩ :=
          callEntryErased info source target relation dest link program lookup
        refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace, by simp [callCredit, zero],
          LoopCase.stateRel_emptyEnv info source target relation, ?_, by simp⟩
        have targetZero : target.clock = 0 := clockEq.trans zero
        have update : {target with clock := 0} = target := by rw [← targetZero]
        cases handler with
        | none =>
            simp only [comp, Nat.add_zero, targetZero, update,
              StackSemEvaluate.evaluate_call, targetLookup, if_true]
        | some triple =>
            obtain ⟨h, hl1, hl2⟩ := triple
            simp only [comp, Nat.add_zero, targetZero, update,
              StackSemEvaluate.evaluate_call, targetLookup, if_true]
      · simp only [zero, if_false] at execution
        rw [StackSemEvaluateClock.fixClockEvaluate] at execution
        rcases bodyExecution : StackSemEvaluate.evaluate
          (program, decClock (setVar link (.loc l1 l2) source)) with
          ⟨bodyResult, middle⟩
        rw [bodyExecution] at execution
        have bodyNonerror : bodyResult ≠ some .error := by
          intro equal
          rw [equal] at execution
          simp only [Prod.mk.injEq] at execution
          exact nonerror execution.1.symm
        obtain ⟨entryInfo, targetLookup, firstClock, targetMiddle, firstSpace,
          firstBudget, middleRelation, calleeExecution, firstGuard⟩ :=
          simulateReturningCallee dest link l1 l2 info source target middle program bodyResult
            calleeIH relation lookup zero bodyExecution bodyNonerror
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + firstClock ≠ 0 := by omega
        have calleeNative : StackSemEvaluate.evaluate
            (compTop entryInfo program, decClock (setVar link (.loc l1 l2)
              {target with clock := target.clock + firstClock})) =
            (bodyResult, {targetMiddle with stackSpace := firstSpace}) := by
          rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
          exact calleeExecution
        cases bodyResult with
        | none =>
            simp only [Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
        | some value =>
            cases value with
            | error => exact False.elim (bodyNonerror rfl)
            | «break» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | «continue» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | halt value =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, by simpa only [callCredit, zero, if_false] using firstBudget, middleRelation, ?_, firstGuard⟩
                cases handler with
                | none =>
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
            | timeOut =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, by simpa only [callCredit, zero, if_false] using firstBudget, middleRelation, ?_, firstGuard⟩
                cases handler with
                | none =>
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
            | finalFFI event =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, by simpa only [callCredit, zero, if_false] using firstBudget, middleRelation, ?_, firstGuard⟩
                cases handler with
                | none =>
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
            | result value =>
                by_cases equal : value = .loc l1 l2
                · subst value
                  simp only [ne_eq, not_true_eq_false, if_false] at execution
                  have spaceEq := firstGuard (by simp)
                  subst firstSpace
                  have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                      targetMiddle := by cases targetMiddle; rfl
                  rw [selfSpace] at calleeExecution
                  obtain ⟨secondClock, targetPost, finalSpace, secondBudget, postRelation,
                    continuationExecution, finalGuard⟩ :=
                    returnIH program lookup zero middle bodyExecution info targetMiddle post result
                      ⟨execution, nonerror, middleRelation⟩
                  have extended := extendReturningCallee (compTop entryInfo program) target
                    targetMiddle (some (.result (.loc l1 l2))) link l1 l2 firstClock secondClock
                    targetNonzero calleeExecution (by simp)
                  have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                  have decrease := StackSemEvaluateClock.evaluateClock ret middle result post execution
                  refine ⟨firstClock + secondClock, targetPost, finalSpace, by
                    simp only [callCredit, zero, if_false]
                    omega, postRelation, ?_, finalGuard⟩
                  cases handler with
                  | none =>
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        totalNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                      simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        totalNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                      simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                  exact False.elim (nonerror execution.1.symm)
            | exception value =>
                cases handler with
                | none =>
                    simp only [Prod.mk.injEq] at execution
                    obtain ⟨rfl, rfl⟩ := execution
                    refine ⟨firstClock, targetMiddle, firstSpace, by simpa only [callCredit, zero, if_false] using firstBudget, middleRelation, ?_, firstGuard⟩
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                      addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    by_cases equal : value = .loc hl1 hl2
                    · subst value
                      simp only [ne_eq, not_true_eq_false, if_false] at execution
                      have spaceEq := firstGuard (by simp)
                      subst firstSpace
                      have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                          targetMiddle := by cases targetMiddle; rfl
                      rw [selfSpace] at calleeExecution
                      obtain ⟨secondClock, targetPost, finalSpace, secondBudget, postRelation,
                        continuationExecution, finalGuard⟩ :=
                        exceptionIH program h hl1 hl2 lookup zero rfl middle bodyExecution
                          info targetMiddle post result ⟨execution, nonerror, middleRelation⟩
                      have extended := extendReturningCallee (compTop entryInfo program) target
                        targetMiddle (some (.exception (.loc hl1 hl2))) link l1 l2
                        firstClock secondClock targetNonzero calleeExecution (by simp)
                      have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                      have decrease := StackSemEvaluateClock.evaluateClock h middle result post execution
                      refine ⟨firstClock + secondClock, targetPost, finalSpace, by
                        simp only [callCredit, zero, if_false]
                        omega, postRelation, ?_, finalGuard⟩
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        totalNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                      simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                    · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                      exact False.elim (nonerror execution.1.symm)

end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.simulateReturningCallee
#print axioms InitECandidate.Solver.StackRawCallBound.compCorrectCallReturn
