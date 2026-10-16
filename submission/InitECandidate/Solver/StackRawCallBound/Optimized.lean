import InitECandidate.Solver.StackRawCallBound.Common

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.SeqCase

-- Strengthening of the pinned optimized-sequence proof: the guarded second
-- induction hypothesis reserves the source call decrement to pay for growth.
theorem simulateOptimizedSeq {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (frame : sptLookup dest info = some allocated)
    (secondIH : BoundedSeqSecondIH C F (.stackFree released) (.call none (.inl dest) none) source)
    (hypothesis : StackSemEvaluate.evaluate
        (.seq (.stackFree released) (.call none (.inl dest) none), source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - post.clock) (optimizedSeq released allocated dest) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have originalRelation := relation
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  have targetSpace : target.stackSpace = source.stackSpace := by rw [targetEq]
  have targetClock : target.clock = source.clock := by rw [targetEq]
  have clockSelf : {target with clock := target.clock + 0} = target := by cases target; simp
  rw [evaluateSeqUnclamped, StackSemEvaluate.evaluate_stackFree] at execution
  by_cases enabled : source.useStack = true
  · simp only [enabled, Bool.not_true, Bool.false_eq_true, if_false] at execution
    by_cases badBounds : source.stack.length < source.stackSpace + released
    · simp only [badBounds, if_true, Prod.mk.injEq] at execution
      exact False.elim (nonerror execution.1.symm)
    · simp only [badBounds, if_false] at execution
      have firstRun : StackSemEvaluate.evaluate (.stackFree released, source) =
          (none, {source with stackSpace := source.stackSpace + released}) := by
        simp [StackSemEvaluate.evaluate_stackFree, enabled, badBounds]
      have shiftedRelation := stateRel_setStackSpace info source target originalRelation
        (source.stackSpace + released)
      have targetEnabled : target.useStack = true := by simpa only [targetEq] using enabled
      have targetBounds : target.stackSpace + released ≤ target.stack.length := by
        simpa only [targetEq] using (show source.stackSpace + released ≤ source.stack.length by omega)
      obtain ⟨body, sourceEntry⟩ := frames dest allocated frame
      obtain ⟨entryInfo, _, targetLookup⟩ := RawCallCase.rawCallEntry info source target originalRelation
        dest (.stackAlloc allocated) body sourceEntry
      have targetEntry : sptLookup dest target.code =
          some (.seq (.stackAlloc allocated) (comp entryInfo body)) := by
        simpa only [comp] using targetLookup
      replace execution : StackSemEvaluate.evaluate (.call none (.inl dest) none,
          {source with stackSpace := source.stackSpace + released}) = (result, post) := by
        simpa only [enabled] using execution
      have callExecution := execution
      rw [evaluateCallAlloc dest allocated body
        {source with stackSpace := source.stackSpace + released} sourceEntry] at execution
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        let targetPost := emptyEnv {target with stackSpace := source.stackSpace + released}
        refine ⟨0, targetPost,
          (if allocated < released then target.stackSpace + (released - allocated)
           else target.stackSpace), by omega, ?_, ?_, by simp⟩
        · simpa only [zero] using LoopCase.stateRel_emptyEnv info
            {source with stackSpace := source.stackSpace + released}
            {target with stackSpace := source.stackSpace + released} shiftedRelation
        · rw [clockSelf]
          simpa only [targetPost, emptyEnv] using
            zeroOptimization released allocated dest (comp entryInfo body) target targetEntry
              targetEnabled targetBounds (targetClock.trans zero)
      · simp only [zero, if_false,
          if_neg (show ¬ (!source.useStack) = true by simp [enabled])] at execution
        by_cases failure : source.stackSpace + released < allocated
        · simp only [failure, if_true, Prod.mk.injEq] at execution
          obtain ⟨rfl, rfl⟩ := execution
          let targetPost := emptyEnv (decClock {target with
            stackSpace := source.stackSpace + released})
          refine ⟨0, targetPost, target.stackSpace, by omega,
            LoopCase.stateRel_emptyEnv info _ _
              (LoopCase.stateRel_decClock info _ _ shiftedRelation), ?_, by simp⟩
          rw [clockSelf]
          simpa only [targetPost, emptyEnv, decClock] using
            failedOptimization released allocated dest target targetEnabled
              (by simpa only [targetSpace] using failure) (by simpa only [targetClock] using zero)
        · obtain ⟨clock, targetPost, finalSpace, budget, postRelation, targetRun, guard⟩ :=
            secondIH {source with stackSpace := source.stackSpace + released} firstRun
              info {target with stackSpace := source.stackSpace + released} post result
              ⟨callExecution, nonerror, shiftedRelation⟩
          change StackSemEvaluate.evaluate (.call none (.inl dest) none,
            {{target with stackSpace := source.stackSpace + released} with
              clock := target.clock + clock}) = (result, {targetPost with stackSpace := finalSpace}) at targetRun
          have callInput : {{target with stackSpace := source.stackSpace + released} with
              clock := target.clock + clock} =
              {{target with clock := target.clock + clock} with
                stackSpace := target.stackSpace + released} := by rw [targetSpace]
          rw [callInput] at targetRun
          have transport := successfulOptimization released allocated dest (comp entryInfo body)
            {target with clock := target.clock + clock} targetEntry targetEnabled targetBounds
            (by simpa only [targetSpace] using (show allocated ≤ source.stackSpace + released by omega))
            (by simp only; rw [targetClock]; omega)
          have combinedInput : {{target with clock := target.clock + clock} with
              clock := ({target with clock := target.clock + clock}).clock +
                (if released < allocated then 1 else 0)} =
              {target with clock := target.clock + (clock + (if released < allocated then 1 else 0))} := by
            simp only [Nat.add_assoc]
          rw [combinedInput] at transport
          refine ⟨clock + (if released < allocated then 1 else 0), targetPost, finalSpace,
            by
              simp only [callCredit, zero, if_false] at budget
              split <;> omega, postRelation, ?_, guard⟩
          rw [transport]
          exact targetRun
  · have disabled : source.useStack = false := by cases source.useStack <;> simp_all
    simp only [disabled, Bool.not_false, if_true, Prod.mk.injEq] at execution
    exact False.elim (nonerror execution.1.symm)


end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.simulateOptimizedSeq
