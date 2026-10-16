import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.JumpLower

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.JumpLower
open Flapjack Compiler.Backend.StackLang Compiler.Encoders.Asm StackSemEvaluate StackSemStateOps

theorem compCorrectJumpLower {width : Nat} [NeZero width] {C F : Type}
    (first second label : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (left right : BitVec width) (program : HolProg width),
      getVar first source = some (.word left) → getVar second source = some (.word right) →
      wordCmpHOL .lower left right = true → sptLookup label source.code = some program →
      source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ StackProps.regBound program k →
      ∃ clock postTarget, clock ≤ resultBudget r ∧
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.jumpLower first second label, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.jumpLower first second label : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer (.jumpLower first second label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer at bound
  have readFirst := RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩
  have readSecond := RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2⟩
  change source.regs.lookup first = target.regs.lookup first at readFirst
  change source.regs.lookup second = target.regs.lookup second at readSecond
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_jumpLower] at sourceRun
  cases hFirst : getVar first source with
  | none =>
    simp only [hFirst] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some left =>
    cases left with
    | loc name offset =>
      simp only [hFirst] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word left =>
      cases hSecond : getVar second source with
      | none =>
        simp only [hFirst, hSecond] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some right =>
        cases right with
        | loc name offset =>
          simp only [hFirst, hSecond] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word right =>
          simp only [hFirst, hSecond] at sourceRun
          have targetFirst : target.regs.lookup first = some (.word left) := readFirst.symm.trans hFirst
          have targetSecond : target.regs.lookup second = some (.word right) := readSecond.symm.trans hSecond
          by_cases lower : wordCmpHOL .lower left right = true
          · simp only [lower, if_true, StackSemControl.findCode] at sourceRun
            cases lookup : sptLookup label source.code with
            | none =>
              simp only [lookup] at sourceRun
              exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
            | some program =>
              simp only [lookup] at sourceRun
              obtain ⟨targetLookup, bodyBound⟩ := FindCode.codeLookup jump bounds pointer label source target program relation lookup
              by_cases zero : source.clock = 0
              · simp only [zero, if_true] at sourceRun
                rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
                subst result
                subst postSource
                refine ⟨0, emptyEnv target, Nat.zero_le _, ?_, ?_⟩
                · simpa only [comp, Nat.zero_add] using
                    (evaluate_jumpLower first second label target).trans (by
                      simp only [getVar, targetFirst, targetSecond, lower, if_true,
                        StackSemControl.findCode, targetLookup, clocks, zero])
                · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
              · simp only [zero, if_false] at sourceRun
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
                    calleeIH left right program hFirst hSecond lower lookup zero bodyResult middle
                      (decClock target) pointer bounds jump
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
                  rw [evaluate_jumpLower]
                  simp only [getVar, targetFirst, targetSecond, StackSemControl.findCode,
                    targetLookup, lower, if_true, nonzero, if_false]
                  rw [clockEq, targetRun]
                  simp [bad]
          · simp [lower] at sourceRun
            rcases sourceRun with ⟨resultEq, postEq⟩
            subst result
            subst postSource
            refine ⟨0, target, Nat.zero_le _, ?_, relation⟩
            simpa only [comp, Nat.zero_add] using
              (evaluate_jumpLower first second label target).trans (by
                simp [getVar, targetFirst, targetSecond, lower])
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectJumpLower
