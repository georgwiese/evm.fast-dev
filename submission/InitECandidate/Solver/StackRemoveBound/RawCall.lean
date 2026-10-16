import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.RawCall

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.RawCall
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

theorem compCorrectRawCall {width : Nat} [NeZero width] {C F : Type}
    (label : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (frame body : HolProg width),
      sptLookup label source.code = some (.seq frame body) → source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ StackProps.regBound body k →
      ∃ clock postTarget, clock ≤ resultBudget r ∧
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.rawCall label, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.rawCall label : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer (.rawCall label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_rawCall] at sourceRun
  cases lookup : sptLookup label source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    cases shape : StackSemControl.destSeq program with
    | none =>
      simp only [shape] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | some pair =>
      rcases pair with ⟨frame, body⟩
      have programEq : program = .seq frame body := by
        cases program <;> simp [StackSemControl.destSeq] at shape ⊢
        exact ⟨shape.1, shape.2⟩
      subst program
      simp only [StackSemControl.destSeq] at sourceRun
      obtain ⟨targetLookup, programBound⟩ := FindCode.findCodeLemma jump bounds pointer
        source target (.inl label) (.seq frame body) ⟨relation, True.intro, lookup⟩
      change sptLookup label target.code = some (comp jump bounds pointer (.seq frame body)) at targetLookup
      simp only [comp] at targetLookup
      change StackProps.regBound frame pointer ∧ StackProps.regBound body pointer at programBound
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, emptyEnv target, Nat.zero_le _, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_rawCall label target).trans (by
              simp only [targetLookup, StackSemControl.destSeq, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
      · simp only [zero, if_false] at sourceRun
        rcases bodyRun : evaluate (body, decClock source) with ⟨bodyResult, middle⟩
        rw [bodyRun] at sourceRun
        by_cases bad : StackSemControl.badFunReturn bodyResult = true
        · simp only [bad, if_true] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        · simp [bad] at sourceRun
          rcases sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, smallClock, targetRun, postRelation⟩ :=
            calleeIH frame body lookup zero bodyResult middle (decClock target) pointer bounds jump
              ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, programBound.2⟩
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
          rw [evaluate_rawCall]
          simp only [targetLookup, StackSemControl.destSeq, nonzero, if_false]
          rw [clockEq, targetRun]
          simp [bad]
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectRawCall
