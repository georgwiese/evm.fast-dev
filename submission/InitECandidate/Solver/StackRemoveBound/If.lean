import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.If

/-! Preserve the result-dependent extra-clock bound through control flow. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.If
open Flapjack Compiler.Backend.StackLang Compiler.Encoders.Asm StackSemEvaluate StackSemStateOps

theorem compCorrectIf {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : HolRegImm width)
    (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (firstIH : ∀ (left right : WordLocW width),
      getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some true →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound first k →
      ∃ clock postTarget, clock ≤ resultBudget r ∧
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (secondIH : ∀ (left right : WordLocW width),
      getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some false →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound second k →
      ∃ clock postTarget, clock ≤ resultBudget r ∧
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.ite comparison register operand first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.ite comparison register operand first second) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer (.ite comparison register operand first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  simp only [StackProps.regBound] at lower
  have leftEq := RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower.1⟩
  have rightEq := operandLookup jump bounds pointer source target operand relation lower.2.1
  rw [evaluate_ite] at sourceRun
  cases leftLookup : getVar register source with
  | none =>
    rw [leftLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some left =>
    rw [leftLookup] at sourceRun
    cases rightLookup : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source with
    | none =>
      rw [rightLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some right =>
      rw [rightLookup] at sourceRun
      simp only [] at sourceRun
      cases compared : wordSemWordCmp comparison left right with
      | none =>
        rw [compared] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | some truth =>
        cases truth with
        | false =>
          rw [compared] at sourceRun
          obtain ⟨clock, postTarget, small, targetRun, postRelation⟩ :=
            secondIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.2⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, postTarget, small, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
        | true =>
          rw [compared] at sourceRun
          obtain ⟨clock, postTarget, small, targetRun, postRelation⟩ :=
            firstIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.1⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, postTarget, small, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectIf
