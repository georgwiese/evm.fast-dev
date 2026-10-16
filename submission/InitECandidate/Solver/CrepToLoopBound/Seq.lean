import InitECandidate.Solver.CrepToLoopBound.Budget
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Seq

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem simulateSeq {width : Nat} [NeZero width] {σ : Type}
    (limit : Nat) (context : CrepToLoopContextExact) (live : NumSet)
    (first second : CrepProgHOL width)
    (source : CrepSemHOLState width σ)
    (safe : CodeSafe limit source.code) (bounded : ceiling (.seq first second) ≤ limit)
    (ihSecond : ∀ firstResult firstState,
      (firstResult, firstState) = evalCrepSemHOLProgExact source first →
      firstResult = none → Simulation limit second firstState)
    (ihFirst : Simulation limit first source)
    (target : LoopSemStateFiniteExact width σ)
    (result : Option (CrepResultHOLExact width))
    (sourceFinal : CrepSemHOLState width σ)
    (hEval : evalCrepSemHOLProgExact source (.seq first second) = (result, sourceFinal))
    (hNotError : result ≠ some .error)
    (hState : crepToLoopStateRelExact source target)
    (hMem : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (hCode : crepToLoopCodeRelExact context source.code target.code)
    (hLocals : crepToLoopLocalsRelExact context live source.locals target.locals) :
    ∃ (extra : Nat) (targetResult : Option (LoopResultExact width))
      (targetFinal : LoopSemStateFiniteExact width σ),
      extra ≤ (2 * limit + 3) * (source.clock - sourceFinal.clock) + cost (.seq first second) ∧
      LoopSemStateFiniteExact.evaluate (compileHOLExact context live (.seq first second))
          { target with clock := target.clock + extra } = (targetResult, targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact context sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧
      localsResultRel context live result sourceFinal targetFinal := by
  have bounds := seqCeiling first second limit bounded
  rw [evalCrepSemHOLProgExact_seq_holShape] at hEval
  cases hFirst : evalCrepSemHOLProgExact source first with
  | mk firstResult firstState =>
    rw [hFirst] at hEval
    cases firstResult with
    | none =>
      simp only at hEval
      obtain ⟨firstExtra, firstTargetResult, firstTargetFinal,
        firstBudget, hFirstRun, hFirstState, hFirstMem, hFirstGlobals, hFirstCode,
        hFirstResult, hFirstLocals⟩ :=
        ihFirst safe bounds.1 none firstState target context live hFirst (by simp)
          hState hMem hGlobals hCode hLocals
      have hFirstTargetNone : firstTargetResult = none := by
        simpa [resultToLoop] using hFirstResult
      subst firstTargetResult
      obtain ⟨secondExtra, finalTargetResult, finalTarget,
        secondBudget, hSecondRun, hSecondState, hSecondMem, hSecondGlobals, hSecondCode,
        hSecondResult, hSecondLocals⟩ :=
        (ihSecond none firstState hFirst.symm rfl)
          (codeSafe_evaluate safe hFirst) bounds.2 result sourceFinal firstTargetFinal context live hEval hNotError
          hFirstState hFirstMem hFirstGlobals hFirstCode hFirstLocals
      have hFirstRunLift :
          LoopSemStateFiniteExact.evaluate (compileHOLExact context live first)
            { target with clock := target.clock + (firstExtra + secondExtra) } =
              (none, { firstTargetFinal with
                clock := firstTargetFinal.clock + secondExtra }) := by
        have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
          (compileHOLExact context live first)
          { target with clock := target.clock + firstExtra } none firstTargetFinal
          secondExtra hFirstRun (by simp)
        simpa [Nat.add_assoc] using hLift
      have totalBudget := composeBudget (2 * limit + 3) source.clock firstState.clock
        sourceFinal.clock firstExtra secondExtra (cost first) (cost second)
        (clockDecrease hFirst) (clockDecrease hEval) firstBudget secondBudget
      refine ⟨firstExtra + secondExtra, finalTargetResult, finalTarget, totalBudget, ?_,
        hSecondState, hSecondMem, hSecondGlobals, hSecondCode,
        hSecondResult, hSecondLocals⟩
      rw [compileHOLExact, LoopSemStateFiniteExact.evaluate_seq, hFirstRunLift]
      exact hSecondRun
    | some firstValue =>
      have hFirstPair : (some firstValue, firstState) = (result, sourceFinal) := by
        simpa using hEval
      rcases Prod.mk.inj hFirstPair with ⟨hResultEq, hFinalEq⟩
      have hFirstNotError : some firstValue ≠ some .error := by
        intro h
        apply hNotError
        rw [← hResultEq]
        exact h
      obtain ⟨extra, targetResult, targetFinal,
        budget, hRun, hFinalState, hFinalMem, hFinalGlobals, hFinalCode,
        hResultMap, hFinalLocals⟩ :=
        ihFirst safe bounds.1 (some firstValue) firstState target context live hFirst hFirstNotError
          hState hMem hGlobals hCode hLocals
      have hFinalState' : crepToLoopStateRelExact sourceFinal targetFinal :=
        hFinalEq ▸ hFinalState
      have hFinalMem' : crepToLoopMemRelHOLExact sourceFinal.memory
          targetFinal.memory sourceFinal.memaddrs := hFinalEq ▸ hFinalMem
      have hFinalGlobals' : crepToLoopGlobalsRelHOLExact sourceFinal.globals
          targetFinal.globals := hFinalEq ▸ hFinalGlobals
      have hFinalCode' : crepToLoopCodeRelExact context sourceFinal.code
          targetFinal.code := hFinalEq ▸ hFinalCode
      have hFinalLocals' : localsResultRel context live result sourceFinal targetFinal := by
        simpa [← hResultEq] using (hFinalEq ▸ hFinalLocals)
      have hTargetSome : targetResult ≠ none := by
        rw [hResultMap]
        cases firstValue <;> simp [resultToLoop]
      have hResultMap' : targetResult = resultToLoop result := by
        simpa [← hResultEq] using hResultMap
      have totalBudget : extra ≤ (2 * limit + 3) * (source.clock - sourceFinal.clock) + cost (.seq first second) := by
        rw [← hFinalEq]
        simp only [cost]
        omega
      refine ⟨extra, targetResult, targetFinal, totalBudget, ?_, hFinalState', hFinalMem',
        hFinalGlobals', hFinalCode', hResultMap', hFinalLocals'⟩
      rw [compileHOLExact, LoopSemStateFiniteExact.evaluate_seq, hRun]
      cases targetResult with
      | none => exact False.elim (hTargetSome rfl)
      | some value => rfl

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.simulateSeq
