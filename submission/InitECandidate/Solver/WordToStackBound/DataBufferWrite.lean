import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.DataBufferWrite

namespace InitECandidate.Solver.WordToStackBound.DataBufferWrite
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.DataBufferWrite

theorem compCorrectDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (r1 r2 : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.dataBufferWrite r1 r2) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨w1,w2,cb,read1,read2,writeEq,rfl,rfl⟩ :=
    sourceSuccess r1 r2 source sourcePost result execution notError
  have evens : r1%2=0 ∧ r2%2=0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 r1 (k,f,frame) with ⟨xs,reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 r2 (k,f,frame) with ⟨ys,reg2⟩
  obtain ⟨t1,run1,clock1,rel1,_,_,_,_,regNe,loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame r1 reg1 xs source target lens
      (.word w1) fmt1 evens.1 read1 related
  obtain ⟨t2,run2,clock2,_,rel2,_,_,otherReads,_,loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame r2 reg2 ys source t1 lens
      (.word w2) fmt2 evens.2 read2 rel1
  have read1Final : StackSemStateOps.getVar reg1 t2 = some (.word w1) := by
    rw [otherReads reg1 regNe]
    exact loaded1
  have bufferEq : t2.dataBuffer = source.dataBuffer :=
    rel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have capacity : cb.buffer.length+cb.spaceLeft = source.dataBuffer.buffer.length+source.dataBuffer.spaceLeft := by
    unfold wordSemBufferWrite at writeEq
    split at writeEq
    · rename_i guard
      have equal := Option.some.inj writeEq
      subst cb
      simp only [List.length_append,List.length_singleton]
      omega
    · cases writeEq
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,fmt1,fmt2] at programEq
  subst compiled
  refine ⟨0,{t2 with dataBuffer := cb},none,Nat.zero_le _,?_,?_⟩
  · simp only [Nat.add_zero,wStackLoadAppend,Function.comp_apply]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)),t1) = (none,t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)),t2) = (none,t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix2]
    have useStack : t2.useStack = true := rel2.2.2.2.2.1
    simp only [StackSemEvaluate.evaluate_dataBufferWrite,useStack,not_true_eq_false,if_false,read1Final,loaded2,bufferEq,writeEq]
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte] using dataBufferRelation cb capacity rel2

end InitECandidate.Solver.WordToStackBound.DataBufferWrite
#print axioms InitECandidate.Solver.WordToStackBound.DataBufferWrite.compCorrectDataBufferWrite
