import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackMemoryAny

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemoryAny
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

theorem compCorrectStackLoadAny {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackLoadAny register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackLoadAny register index : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoadAny register index),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_stackLoadAny] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  cases indexLookup : StackSemStateOps.getVar index source with
  | none =>
    rw [indexLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    cases value with
    | loc block offset =>
      rw [indexLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | word word =>
      rw [indexLookup] at sourceRun
      dsimp only at sourceRun
      by_cases valid : source.stackSpace + (word >>> wordShiftAmount width).toNat < source.stack.length ∧
          (word >>> wordShiftAmount width) <<< wordShiftAmount width = word
      · rw [dif_pos valid] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
        subst result
        subst postSource
        have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have offsetEq := alignedOffset word good valid.2
        have targetIndex : target.regs.lookup index = some (.word word) := by
          change StackSemStateOps.getVar index target = some (.word word)
          rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
          exact indexLookup
        obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
        let pointerWord := base + bytesInWord width * BitVec.ofNat width source.stackSpace
        change target.regs.lookup pointer = some (.word pointerWord) at pointerLookup
        have addressEq : word + pointerWord = base + wordOffset (source.stackSpace + (word >>> wordShiftAmount width).toNat) := by
          calc
            word + pointerWord = wordOffset (word >>> wordShiftAmount width).toNat + pointerWord := by
              rw [offsetEq]
            _ = _ := by
              dsimp [pointerWord]
              simp only [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add]
              rw [BitVec.add_comm (bytesInWord width * BitVec.ofNat width (word >>> wordShiftAmount width).toNat),
                BitVec.add_assoc]
        let entry := source.stack[source.stackSpace + (word >>> wordShiftAmount width).toNat]
        have read : StackSemStateOps.memLoad (word + pointerWord) target = some entry := by
          rw [addressEq]
          exact reads _ valid.1
        refine ⟨0, StackSemStateOps.setVar register entry target, Nat.zero_le _, ?_, ?_⟩
        · simp only [Nat.zero_add]
          rw [comp, StackSemEvaluate.evaluate_seq,
            runMoveAdd target register index pointer word pointerWord targetIndex pointerLookup (by omega)]
          simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
          let addressed := StackSemStateOps.setVar register (.word (word + pointerWord)) target
          have addressedLookup : addressed.regs.lookup register = some (.word (word + pointerWord)) := by
            simp [addressed, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          have addressedRead : StackSemStateOps.memLoad (word + pointerWord + 0) addressed = some entry := by
            simpa [addressed, StackSemStateOps.memLoad, StackSemStateOps.setVar] using read
          change StackSemEvaluate.evaluate (.inst (.mem .load register (.addr register 0)), addressed) = _
          rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemory.runLoad addressed register register _ 0 entry addressedLookup addressedRead]
          simp only [addressed, StackFreeSimulation.setVarTwice]
          rfl
        · simpa only [entry, relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
            entry source target ⟨relation, lower.1⟩
      · rw [dif_neg valid] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
/-- Flapjack native execution factoring for the original Any constructors;
all lookup facts are derived inside the full cases below. No standalone HOL
declaration is claimed. -/
theorem runAdd {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (destination left right : Nat)
    (first second : BitVec width)
    (leftLookup : state.regs.lookup left = some (.word first))
    (rightLookup : state.regs.lookup right = some (.word second)) :
    StackSemEvaluate.evaluate (.inst (.arith (.binop .add destination left (.reg right))), state) =
      (none, StackSemStateOps.setVar destination (.word (first + second)) state) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp,
    leftLookup, rightLookup, wordOpHOL, wordOp]
/-- Flapjack native execution factoring for the original Any constructors;
all lookup facts are derived inside the full cases below. No standalone HOL
declaration is claimed. -/
theorem runSub {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (destination left right : Nat)
    (first second : BitVec width)
    (leftLookup : state.regs.lookup left = some (.word first))
    (rightLookup : state.regs.lookup right = some (.word second)) :
    StackSemEvaluate.evaluate (.inst (.arith (.binop .sub destination left (.reg right))), state) =
      (none, StackSemStateOps.setVar destination (.word (first - second)) state) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp,
    leftLookup, rightLookup, wordOpHOL, wordOp]
/-- Genuine full original StackStoreAny compiler constructor. The source
alignment/index guard derives actual native heap access and the complete
postrelation; no target-access, postheap or pointer-restoration premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackStoreAny {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackStoreAny register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackStoreAny register index : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStoreAny register index),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_stackStoreAny] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  cases valueLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [valueLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [valueLookup] at sourceRun
    cases indexLookup : StackSemStateOps.getVar index source with
    | none =>
      rw [indexLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some indexValue =>
      cases indexValue with
      | loc block offset =>
        rw [indexLookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | word word =>
        rw [indexLookup] at sourceRun
        dsimp only at sourceRun
        by_cases valid : source.stackSpace + (word >>> wordShiftAmount width).toNat < source.stack.length ∧
            (word >>> wordShiftAmount width) <<< wordShiftAmount width = word
        · rw [if_pos valid] at sourceRun
          rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
          subst result
          subst postSource
          have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have offsetEq := alignedOffset word good valid.2
          have pointerNeRegister : register ≠ pointer := by omega
          have pointerNeIndex : index ≠ pointer := by omega
          have targetValue : target.regs.lookup register = some value := by
            change StackSemStateOps.getVar register target = some value
            rw [← RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower.1⟩]
            exact valueLookup
          have targetIndex : target.regs.lookup index = some (.word word) := by
            change StackSemStateOps.getVar index target = some (.word word)
            rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
            exact indexLookup
          obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
          let pointerWord := base + bytesInWord width * BitVec.ofNat width source.stackSpace
          change target.regs.lookup pointer = some (.word pointerWord) at pointerLookup
          have addressEq : pointerWord + word = base + wordOffset (source.stackSpace + (word >>> wordShiftAmount width).toNat) := by
            calc
              pointerWord + word = pointerWord + wordOffset (word >>> wordShiftAmount width).toNat := by rw [offsetEq]
              _ = _ := by
                dsimp [pointerWord]
                simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
          have read : StackSemStateOps.memLoad (pointerWord + word) target =
              some source.stack[source.stackSpace + (word >>> wordShiftAmount width).toNat] := by
            rw [addressEq]
            exact reads _ valid.1
          have domain : target.mdomain (pointerWord + word) = true := by
            by_contra outside
            simp [StackSemStateOps.memLoad, outside] at read
          let updated := {target with memory := fun key => if key = pointerWord + word then value else target.memory key}
          refine ⟨0, updated, Nat.zero_le _, ?_, ?_⟩
          · simp only [Nat.zero_add]
            rw [comp, StackSemEvaluate.evaluate_seq,
              runAdd target pointer pointer index pointerWord word pointerLookup targetIndex]
            simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
            let shifted := StackSemStateOps.setVar pointer (.word (pointerWord + word)) target
            have shiftedPointer : shifted.regs.lookup pointer = some (.word (pointerWord + word)) := by
              simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
            have shiftedValue : shifted.regs.lookup register = some value := by
              simpa [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, pointerNeRegister] using targetValue
            have shiftedDomain : shifted.mdomain (pointerWord + word + 0) = true := by
              simpa [shifted, StackSemStateOps.setVar] using domain
            change StackSemEvaluate.evaluate (.seq (.inst (.mem .store register (.addr pointer 0)))
              (.inst (.arith (.binop .sub pointer pointer (.reg index)))), shifted) = _
            rw [StackSemEvaluate.evaluate_seq,
              Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemory.runStore shifted register pointer _ 0 value shiftedPointer shiftedValue shiftedDomain]
            simp only [StackSemControl.fixClock, Nat.min_self]
            let written := {shifted with memory := fun key => if key = pointerWord + word + 0 then value else shifted.memory key}
            have writtenPointer : written.regs.lookup pointer = some (.word (pointerWord + word)) := shiftedPointer
            have writtenIndex : written.regs.lookup index = some (.word word) := by
              simpa [written, shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, pointerNeIndex] using targetIndex
            change StackSemEvaluate.evaluate (.inst (.arith (.binop .sub pointer pointer (.reg index))), written) = _
            rw [runSub written pointer pointer index _ word writtenPointer writtenIndex]
            simp only [BitVec.add_sub_cancel]
            have restore : StackSemStateOps.setVar pointer (.word pointerWord) shifted = target := by
              dsimp [shifted]
              rw [StackFreeSimulation.setVarTwice, StackFreeSimulation.setVarExisting target pointer (.word pointerWord) pointerLookup]
            let newMemory : BitVec width → WordLocW width :=
              fun key => if key = (pointerWord + word + 0) then value else target.memory key
            change (none, {(StackSemStateOps.setVar pointer (.word pointerWord) shifted) with memory := newMemory}) = _
            rw [restore]
            simp [updated, newMemory]
          · simpa only [updated, relation.1, Nat.add_comm, offsetEq] using
              StackHeapWrites.stateRelStackStore jump bounds pointer (word >>> wordShiftAmount width).toNat
                source target source.stack pointerWord (pointerWord + word) value
                ⟨relation, rfl, pointerLookup, valid.1, by rw [← WordAddressArithmetic.wordOffsetEq, offsetEq]⟩
        · rw [if_neg valid] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectStackLoadAny
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectStackStoreAny
