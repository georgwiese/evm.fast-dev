import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.OpCurrHeap

namespace InitECandidate.Solver.WordToStackBound.OpCurrHeap
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.OpCurrHeap

private theorem sourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (operator : HolBinop) (dst src : Nat) (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.opCurrHeap operator dst src) source = (result,post))
    (notError : result ≠ some .error) :
    ∃ operand heap value : BitVec width,
      WordSemStateFiniteExact.getVar src source = some (.word operand) ∧
      source.store.lookup .currHeap = some (.word heap) ∧
      wordOpHOL operator [operand,heap] = some value ∧
      result = none ∧ post = WordSemStateFiniteExact.setVar dst (.word value) source := by
  cases read : WordSemStateFiniteExact.getVar src source with
  | none =>
    simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
      read,theWords] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  | some operandValue =>
    cases operandValue with
    | loc l n =>
      simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
        read,theWords] at execution
      obtain ⟨rfl,rfl⟩ := execution
      contradiction
    | word operand =>
      cases heapRead : source.store.lookup .currHeap with
      | none =>
        simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.getStore,read,heapRead,theWords] at execution
        obtain ⟨rfl,rfl⟩ := execution
        contradiction
      | some heapValue =>
        cases heapValue with
        | loc l n =>
          simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getStore,read,heapRead,theWords] at execution
          obtain ⟨rfl,rfl⟩ := execution
          contradiction
        | word heap =>
          cases operation : wordOpHOL operator [operand,heap] with
          | none =>
            simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore,read,heapRead,theWords,operation] at execution
            obtain ⟨rfl,rfl⟩ := execution
            contradiction
          | some value =>
            simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore,read,heapRead,theWords,operation] at execution
            obtain ⟨rfl,rfl⟩ := execution
            exact ⟨operand,heap,value,rfl,rfl,operation,rfl,rfl⟩
/-- Full original OpCurrHeap constructor under the unchanged simulation motive.
Source success supplies both words; the native arithmetic callback is proved
from the full loaded-state relation. Evaluator closure inherits
reals_as_rational_cuts; no independent real-analysis agreement is claimed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectOpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (operator : HolBinop) (dst src : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.opCurrHeap operator dst src) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨operand,heap,value,read,heapRead,operation,rfl,rfl⟩ :=
    sourceSuccess source sourcePost operator dst src result execution notError
  have evens : dst % 2 = 0 ∧ src % 2 = 0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  have dstEq : dst = 2*(dst/2) := by omega
  have bound : dst/2 < frame+k := by
    simp only [maxVarHOL] at maxBound
    omega
  rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 src (k,f,frame) with ⟨loads,reg⟩
  obtain ⟨loaded,loadRun,clockEq,loadRel,_,_,_,_,_,loadedRead⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame src reg loads
      source target lens (.word operand) format evens.2 read related
  have storeEq : source.store = loaded.store.eraseEq .handler :=
    loadRel.2.2.2.2.2.2.2.2.2.2.2.1
  have targetHeap : loaded.store.lookup .currHeap = some (.word heap) := by
    rw [storeEq] at heapRead
    simpa [HolFiniteMapExact.eraseEq,FDOMSUB_HOL] using heapRead
  have useStore : loaded.useStore = true := loadRel.2.2.2.2.2.1
  have callback : ∀ d, d ≤ k →
      StackSemEvaluate.evaluate (.opCurrHeap operator d reg,loaded) =
        (none,StackSemStateOps.setVar d (.word value) loaded) := by
    intro d _
    change loaded.regs.lookup reg = some (.word operand) at loadedRead
    simp [StackSemEvaluate.evaluate_opCurrHeap,useStore,StackSemExpressions.wordExp,
      loadedRead,targetHeap,operation]
  obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
    (dst/2) source loaded lens (.word value) (fun d => .opCurrHeap operator d reg)
    loadRel bound callback
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,format] at programEq
  subst compiled
  refine ⟨0,post,none,Nat.zero_le _,?_,?_⟩
  · simp only [Nat.add_zero,LoadRegister.evaluateWStackLoadSeq,
      StackSemEvaluate.evaluate_seq,loadRun]
    have fix : StackSemControl.fixClock target ((none : Option (StackSemResult width)),loaded) = (none,loaded) := by
      have le : loaded.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix]
    simpa only [← dstEq] using actual
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte,← dstEq] using postRel
end InitECandidate.Solver.WordToStackBound.OpCurrHeap
#print axioms InitECandidate.Solver.WordToStackBound.OpCurrHeap.compCorrectOpCurrHeap
