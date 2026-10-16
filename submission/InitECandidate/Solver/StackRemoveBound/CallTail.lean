import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallTail

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallTail
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

theorem compCorrectCallTail {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (program : HolProg width),
      StackSemControl.findCode dest source.regs source.code = some program →
      handler = none → source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ StackProps.regBound program k →
      ∃ clock postTarget, clock ≤ resultBudget r ∧
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.call none dest handler, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.call none dest handler : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer (.call none dest handler),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_call] at sourceRun
  cases lookup : StackSemControl.findCode dest source.regs source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    cases handler with
    | some h =>
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | none =>
      obtain ⟨targetLookup, bodyBound⟩ := FindCode.findCodeLemma jump bounds pointer
        source target dest program ⟨relation, by
          simp only [StackProps.regBound] at bound
          cases dest <;> exact bound.1, lookup⟩
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, emptyEnv target, Nat.zero_le _, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_call none dest none target).trans (by
              simp only [targetLookup, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
      · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at sourceRun
        rcases bodyRun : evaluate (program, decClock source) with ⟨bodyResult, middle⟩
        rw [bodyRun] at sourceRun
        by_cases bad : StackSemControl.badFunReturn bodyResult = true
        · simp only [bad, if_true] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        · simp [bad] at sourceRun
          rcases sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, smallClock, targetRun, postRelation⟩ :=
            calleeIH program lookup rfl zero bodyResult middle (decClock target) pointer bounds jump
              ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, bodyBound⟩
          refine ⟨clock, postTarget, smallClock, ?_, ?_⟩
          swap
          · cases bodyResult with
            | none => exact postRelation
            | some r => cases r <;> exact postRelation
          have nonzero : clock + target.clock ≠ 0 := by omega
          have clockEq : decClock {target with clock := clock + target.clock} =
              {decClock target with clock := clock + (decClock target).clock} := by
            simp only [decClock]
            congr 1
            omega
          simp only [comp]
          rw [evaluate_call]
          simp only [targetLookup, nonzero, if_false, StackSemEvaluateClock.fixClockEvaluate]
          rw [clockEq, targetRun]
          simp [bad]
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectCallTail
