import InitECandidate.Solver.StackRemoveBound.StoreConsts
import InitECandidate.Bitmaps

/-! Local numeric specialization; bitmap equality is retained as a premise
until the actual initialized source-state proof supplies it. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

set_option maxRecDepth 100000 in
theorem fixedBitmapLength : InitECandidate.bitmaps.length = 4614 := by decide

theorem storeConstsFixedBound {C F : Type} (temporary bitmap : Nat) (stub : Option Nat)
    (source : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (postSource target : StackSemStateFiniteExact 64 C F)
    (pointer : Nat) (bounds : BitVec 64 × BitVec 64) (jump : Bool)
    (fixed : source.bitmaps = InitECandidate.bitmaps)
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts temporary bitmap stub, source) =
      (result, postSource) ∧ result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.storeConsts temporary bitmap stub : HolProg 64) pointer) :
    ∃ clock postTarget, clock ≤ 4614 ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.storeConsts temporary bitmap stub),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  obtain ⟨clock, post, small, run, relation⟩ :=
    compCorrectStoreConsts temporary bitmap stub source result postSource target pointer bounds jump hypothesis
  rw [fixed, fixedBitmapLength] at small
  refine ⟨clock, post, small, run, ?_⟩
  cases result with
  | none => exact relation
  | some value => cases value <;> exact relation

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.fixedBitmapLength
#print axioms InitECandidate.Solver.StackRemoveBound.storeConstsFixedBound
