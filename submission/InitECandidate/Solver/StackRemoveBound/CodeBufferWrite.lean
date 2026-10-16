import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CodeBufferWrite

/-! Expose zero extra clocks in the original guarded Stack-removal case proofs. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.CodeBufferWrite
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

theorem compCorrectCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.codeBufferWrite first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.codeBufferWrite first second : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer (.codeBufferWrite first second),
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
  have buffers : target.codeBuffer = source.codeBuffer := relation.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [evaluate_codeBufferWrite] at sourceRun
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
          cases write : wordSemBufferWrite source.codeBuffer left (right.setWidth 8) with
          | none =>
            simp only [write] at sourceRun
            exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          | some buffer =>
            simp only [write] at sourceRun
            rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
            subst result
            subst postSource
            have targetFirst : target.regs.lookup first = some (.word left) := readFirst.symm.trans hFirst
            have targetSecond : target.regs.lookup second = some (.word right) := readSecond.symm.trans hSecond
            refine ⟨0, {target with codeBuffer := buffer}, Nat.zero_le _, ?_, ?_⟩
            · simpa only [comp, Nat.zero_add] using
                (evaluate_codeBufferWrite first second target).trans (by
                  simp only [getVar, targetFirst, targetSecond, buffers, write])
            · exact stateRelCodeBuffer jump bounds pointer source target buffer relation
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectCodeBufferWrite
