import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Bitmap

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.Bitmap
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

theorem compCorrectBitmapLoad {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.bitmapLoad register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.bitmapLoad register index : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.bitmapLoad register index),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_bitmapLoad] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_or] at sourceRun
  by_cases same : register = index
  · simp only [same, beq_self_eq_true, if_true] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · simp only [beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, if_false] at sourceRun
    cases lookup : StackSemStateOps.getVar index source with
    | none =>
      rw [lookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some value =>
      cases value with
      | loc first second =>
        rw [lookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | word word =>
        rw [lookup] at sourceRun
        simp only [] at sourceRun
        by_cases outsideBounds : source.bitmaps.length ≤ word.toNat
        · rw [dif_pos outsideBounds] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
        · rw [dif_neg outsideBounds] at sourceRun
          have resultEq := (Prod.mk.inj sourceRun).1.symm
          have sourceEq := (Prod.mk.inj sourceRun).2.symm
          subst result
          subst postSource
          have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          obtain ⟨bitmapWord, bitmapLookup, reads⟩ := bitmapReads jump bounds pointer source target relation
          obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heap⟩ :=
            StackPointer.stateRelGetVarK jump bounds pointer source target relation
          have firstRead := StoreHeapReads.memLoadLemma .bitmapBase source target (.word bitmapWord) base
            ⟨by simp [storeList], by simpa only [StackSemRegisterTransfers.storeOfSyntax] using bitmapLookup,
              by simpa only [List.length_append, Nat.add_comm] using heap⟩
          have targetIndex : target.regs.lookup index = some (.word word) := by
            change StackSemStateOps.getVar index target = some (.word word)
            rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
            exact lookup
          have addressEq : (bitmapWord + word) <<< wordShiftAmount width =
              (bitmapWord <<< wordShiftAmount width) + bytesInWord width * BitVec.ofNat width word.toNat := by
            simp only [BitVec.shiftLeft_add_distrib, BitVec.ofNat_toNat, BitVec.setWidth_eq]
            rw [WordAddressArithmetic.lslWordShift word good, BitVec.mul_comm word]
          have bound : word.toNat < source.bitmaps.length := by omega
          have read := reads word.toNat bound
          rw [← addressEq] at read
          refine ⟨0, StackSemStateOps.setVar register (.word source.bitmaps[word.toNat]) target, Nat.zero_le _, ?_, ?_⟩
          · simp only [Nat.zero_add]
            have execution := runBitmap target register index pointer base bitmapWord word source.bitmaps[word.toNat]
              baseLookup targetIndex (Ne.symm same) firstRead read good
            simpa only [comp] using execution
          · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
              (.word source.bitmaps[word.toNat]) source target ⟨relation, lower.1⟩
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectBitmapLoad
