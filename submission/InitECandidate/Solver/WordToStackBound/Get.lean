import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Get

namespace InitECandidate.Solver.WordToStackBound.Get
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Get

theorem compCorrectGet {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (register : Nat) (name : WordStoreHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.get register name) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [WordSemStateFiniteExact.evaluate] at execution
  cases read : WordSemStateFiniteExact.getStore name source with
  | none => simp [read] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
  | some value =>
    simp only [read,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar] using conventions
    have twice : register = 2*(register/2) := by omega
    have bound : register/2 < frame+k := by
      simp only [maxVarHOL] at maxBound
      omega
    have storeRel : source.store = target.store.eraseEq .handler :=
      related.2.2.2.2.2.2.2.2.2.2.2.1
    have targetRead : target.store.lookup (StackSemRegisterTransfers.storeOfSyntax (storeNameOfWord name)) = some value := by
      unfold WordSemStateFiniteExact.getStore at read
      rw [storeRel] at read
      cases name <;>
        simp only [storeNameOfWord,StackSemRegisterTransfers.storeOfSyntax,
          HolFiniteMapExact.eraseEq,FDOMSUB_HOL] at read ⊢ <;>
        simp only [reduceCtorEq,ite_false,ite_true] at read <;>
        exact read
    have useStore : target.useStore = true := related.2.2.2.2.2.1
    have run : ∀ r, r ≤ k → StackSemEvaluate.evaluate (.get r (storeNameOfWord name),target) =
        (none,StackSemStateOps.setVar r value target) := by
      intro r _
      simp [StackSemEvaluate.evaluate_get,useStore,targetRead]
    obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
      (register/2) source target lens value (fun r => .get r (storeNameOfWord name))
      related bound run
    have programEq := congrArg Prod.fst compilation
    simp only [compNative] at programEq
    subst compiled
    refine ⟨0,post,none,Nat.zero_le _,?_,?_⟩
    · simpa only [Nat.add_zero,← twice] using actual
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte,← twice] using postRel
end InitECandidate.Solver.WordToStackBound.Get
#print axioms InitECandidate.Solver.WordToStackBound.Get.compCorrectGet
