import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Set

namespace InitECandidate.Solver.WordToStackBound.Set
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Set

theorem compCorrectSet {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (name : WordStoreHOL)
    (expression : WordLangExpHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.set name expression) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  cases expression <;> simp [flatExpConventions] at flat
  rename_i register
  simp only [WordSemStateFiniteExact.evaluate] at execution
  have notHandler : name ≠ .handler := by
    intro eq; subst name; simp only [true_or,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution; contradiction
  have notBitmap : name ≠ .bitmapBase := by
    intro eq; subst name; simp only [or_true,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution; contradiction
  simp only [notHandler,notBitmap,false_or,if_false,WordSemStateFiniteExact.wordExp] at execution
  cases read : WordSemStateFiniteExact.getVar register source with
  | none => simp [read] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
  | some value =>
    simp only [read,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,everyVarExpHOL,isPhyVar] using conventions
    rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 register (k,f,frame) with ⟨loads,reg⟩
    obtain ⟨loaded,loadRun,clockEq,loadRel,_,_,_,_,_,loadedRead⟩ :=
      LoadRegister.evaluateWStackLoadWReg1 ac k f frame register reg loads
        source target lens value format even read related
    have useStore : loaded.useStore = true := loadRel.2.2.2.2.2.1
    have codec : StackSemRegisterTransfers.storeOfSyntax (storeNameOfWord name) = name := by
      cases name <;> rfl
    have programEq := congrArg Prod.fst compilation
    have compiledEq : compiled = wStackLoadNative loads (.set (storeNameOfWord name) reg) := by
      cases name <;> simp only [compNative,format] at programEq <;>
        first | exact programEq.symm | contradiction
    subst compiled
    refine ⟨0,StackSemStateOps.setStore name value loaded,none,Nat.zero_le _,?_,?_⟩
    · simp only [Nat.add_zero,LoadRegister.evaluateWStackLoadSeq,
        StackSemEvaluate.evaluate_seq,loadRun]
      have fix : StackSemControl.fixClock target ((none : Option (StackSemResult width)),loaded) = (none,loaded) := by
        have le : loaded.clock ≤ target.clock := by omega
        simp only [StackSemControl.fixClock,Nat.min_eq_right le]
      rw [fix]
      simp only [StackSemEvaluate.evaluate_set,useStore,not_true_eq_false,if_false,
        loadedRead,codec]
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte] using StateRelStoreUpdate.stateRelSetStore ac k f frame source
          loaded lens 0 name value notHandler loadRel
end InitECandidate.Solver.WordToStackBound.Set
#print axioms InitECandidate.Solver.WordToStackBound.Set.compCorrectSet
