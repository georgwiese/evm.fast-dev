import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Return

namespace InitECandidate.Solver.WordToStackBound.Return
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Return

theorem compCorrectReturn {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (register : Nat) (names : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.return register names) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maximum⟩
  rw [WordSemStateFiniteExact.evaluate] at execution
  cases sourceRead : WordSemStateFiniteExact.getVar register source with
  | none =>
    simp only [sourceRead, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  | some address =>
    cases address with
    | word word =>
      simp only [sourceRead, Prod.mk.injEq] at execution
      exact absurd execution.1.symm notError
    | loc first second =>
      cases sourceValues : WordSemStateFiniteExact.getVars names source with
      | none =>
        simp only [sourceRead, sourceValues, Prod.mk.injEq] at execution
        exact absurd execution.1.symm notError
      | some values =>
        simp only [sourceRead, sourceValues, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨even, canonical, nameBound, countBound⟩ := returnFacts related conventions maximum
        rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 register (k, f, frame) with ⟨loads, output⟩
        simp only [compNative, format, Prod.mk.injEq] at compilation
        obtain ⟨rfl, _⟩ := compilation
        obtain ⟨loaded, loadRun, clockSame, loadRelated, stackLength, spaceSame, bitmapSame,
          preserved, outputNotScratch, outputValue⟩ :=
          LoadRegister.evaluateWStackLoadWReg1 ac k f frame register output loads
            source target lens (.loc first second) format even sourceRead related
        let count := Compiler.Backend.WordToStack.numStackRet k names
        let free := Compiler.Backend.WordToStack.skipFree k f frame names
        let post : StackSemStateFiniteExact width C F :=
          {loaded with stackSpace := loaded.stackSpace + free}
        have freeSpace : loaded.stackSpace + free = loaded.stackSpace + f - count := by
          dsimp [free, count, Compiler.Backend.WordToStack.skipFree]
          omega
        have useStack : loaded.useStack = true := loadRelated.2.2.2.2.1
        have frameBound : loaded.stackSpace + f ≤ loaded.stack.length := by
          unfold stateRel at loadRelated
          aesop (config := { enableSimp := false })
        have freeBound : loaded.stackSpace + free ≤ loaded.stack.length := by
          dsimp [free, Compiler.Backend.WordToStack.skipFree]
          omega
        refine ⟨0, post, some (.result (.loc first second)), Nat.zero_le _, ?_, ?_⟩
        · simp only [Nat.add_zero]
          rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, loadRun]
          simp only [StackSemControl.fixClock, clockSame, Nat.min_self]
          rw [CallHelpers.evaluateSeqStackFree free (.ret output) loaded
            ⟨useStack, by omega⟩]
          rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_stackFree,
            if_neg (by simp [useStack]), if_neg (by omega)]
          simp only [StackSemControl.fixClock, Nat.min_self]
          rw [StackSemEvaluate.evaluate_ret]
          simp only [StackSemStateOps.getVar] at outputValue ⊢
          rw [outputValue]
        · have lengths := WordSemStateFiniteExact.getVarsLengthLemma names source values sourceValues
          have kLarge : 4 < k := related.2.2.2.2.2.2.2.2.2.1
          have extraEq : values.length - (k - 1) = count := by
            dsimp [count, Compiler.Backend.WordToStack.numStackRet]
            omega
          simp only [compCorrectResult, Option.map_some, compileResult,
            ne_eq, not_true_eq_false, ↓reduceIte]
          constructor
          · rw [extraEq]
            have relation := stateRelReturnFlush loadRelated countBound
            simpa only [post, freeSpace] using relation
          · have placements := returnPlacements loadRelated canonical sourceValues countBound
            simpa only [post, freeSpace] using placements

end InitECandidate.Solver.WordToStackBound.Return
#print axioms InitECandidate.Solver.WordToStackBound.Return.compCorrectReturn
