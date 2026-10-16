import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackMemory

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemory
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

theorem compCorrectStackLoad {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackLoad register count : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackLoad] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases bound : source.stackSpace + count < source.stack.length
  · rw [dif_pos bound] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
    change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
    have addressEq : base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count =
        base + wordOffset (source.stackSpace + count) := by
      simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
    have read : StackSemStateOps.memLoad
        (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count) target =
        some source.stack[source.stackSpace + count] := by
      rw [addressEq]
      exact reads (source.stackSpace + count) bound
    refine ⟨0, StackSemStateOps.setVar register source.stack[source.stackSpace + count] target, Nat.zero_le _, ?_, ?_⟩
    · simp only [Nat.zero_add]
      rw [comp]
      split
      · exact runLoad target register pointer _ _ _ pointerLookup read
      · have moveRun : StackSemEvaluate.evaluate (moveInst register pointer, target) =
            (none, StackSemStateOps.setVar register
              (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) target) := by
          simp [moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
            StackSemIntegerInstructions.instInteger, pointerLookup]
        rw [StackSemEvaluate.evaluate_seq, moveRun]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        let initial := StackSemStateOps.setVar register
          (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) target
        have initialLookup : initial.regs.lookup register =
            some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := by
          simp [initial, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (stackLoad register count, initial) = _
        rw [stackLoad, StackSemEvaluate.evaluate_seq,
          ShiftSimulation.evaluateUpshift count register initial _ initialLookup]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        let shifted := StackSemStateOps.setVar register
          (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count)) initial
        have shiftedLookup : shifted.regs.lookup register =
            some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count)) := by
          simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (.inst (.mem .load register (.addr register 0)), shifted) = _
        have shiftedRead : StackSemStateOps.memLoad
            (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count + 0) shifted =
            some source.stack[source.stackSpace + count] := by
          simpa [shifted, initial, StackSemStateOps.memLoad, StackSemStateOps.setVar] using read
        rw [runLoad shifted register register _ 0 _ shiftedLookup shiftedRead]
        simp only [shifted, initial, StackFreeSimulation.setVarTwice]
        rfl
    · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
        source.stack[source.stackSpace + count] source target ⟨relation, lower⟩
  · rw [dif_neg bound] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
/-- Flapjack primitive-store execution factoring. The full constructor derives
the original register value, pointer lookup and memory-domain facts rather
than taking them as compiler-correctness premises. No standalone HOL declaration. -/
theorem runStore {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register baseReg : Nat)
    (base offset : BitVec width) (value : WordLocW width)
    (baseLookup : state.regs.lookup baseReg = some (.word base))
    (valueLookup : state.regs.lookup register = some value)
    (domain : state.mdomain (base + offset) = true) :
    StackSemEvaluate.evaluate (.inst (.mem .store register (.addr baseReg offset)), state) =
      (none, {state with memory := fun key => if key = base + offset then value else state.memory key}) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.wordExp,
    StackSemStateOps.getVar, baseLookup, valueLookup, wordOpHOL, wordOp,
    StackSemStateOps.memStore, domain]
/-- Genuine full original StackStore constructor, including direct store and
upshift/store/downshift fallback. The actual target memory update and exact
pointer restoration establish the full post-state relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackStore {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackStore register count : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStore register count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackStore] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases outsideBounds : source.stack.length ≤ source.stackSpace + count
  · rw [if_pos outsideBounds] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · rw [if_neg outsideBounds] at sourceRun
    cases sourceLookup : StackSemStateOps.getVar register source with
    | none =>
      rw [sourceLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some value =>
      rw [sourceLookup] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      have safe : source.stackSpace + count < source.stack.length := Nat.lt_of_not_ge outsideBounds
      have different : register ≠ pointer := by omega
      have valueLookup : target.regs.lookup register = some value := by
        change StackSemStateOps.getVar register target = some value
        rw [← RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower⟩]
        exact sourceLookup
      obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
      let pointerWord := base + bytesInWord width * BitVec.ofNat width source.stackSpace
      change target.regs.lookup pointer = some (.word pointerWord) at pointerLookup
      have addressEq : pointerWord + wordOffset count = base + wordOffset (source.stackSpace + count) := by
        dsimp [pointerWord]
        simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
      have read : StackSemStateOps.memLoad (pointerWord + wordOffset count) target =
          some source.stack[source.stackSpace + count] := by
        rw [addressEq]
        exact reads _ safe
      have domain : target.mdomain (pointerWord + wordOffset count) = true := by
        by_contra outside
        simp [StackSemStateOps.memLoad, outside] at read
      let updated := {target with memory := fun key => if key = pointerWord + wordOffset count then value else target.memory key}
      refine ⟨0, updated, Nat.zero_le _, ?_, ?_⟩
      · simp only [Nat.zero_add]
        rw [comp]
        split
        · exact runStore target register pointer _ _ value pointerLookup valueLookup domain
        · rw [stackStore, StackSemEvaluate.evaluate_seq,
            ShiftSimulation.evaluateUpshift count pointer target pointerWord pointerLookup]
          simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
          let shifted := StackSemStateOps.setVar pointer (.word (pointerWord + wordOffset count)) target
          have shiftedPointer : shifted.regs.lookup pointer = some (.word (pointerWord + wordOffset count)) := by
            simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          have shiftedValue : shifted.regs.lookup register = some value := by
            simpa [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using valueLookup
          have shiftedDomain : shifted.mdomain (pointerWord + wordOffset count + 0) = true := by
            simpa [shifted, StackSemStateOps.setVar] using domain
          change StackSemEvaluate.evaluate (.seq (.inst (.mem .store register (.addr pointer 0)))
            (downshift pointer count), shifted) = _
          rw [StackSemEvaluate.evaluate_seq,
            runStore shifted register pointer _ 0 value shiftedPointer shiftedValue shiftedDomain]
          simp only [StackSemControl.fixClock, Nat.min_self]
          let written := {shifted with memory := fun key => if key = pointerWord + wordOffset count + 0 then value else shifted.memory key}
          have writtenPointer : written.regs.lookup pointer = some (.word (pointerWord + wordOffset count)) := shiftedPointer
          change StackSemEvaluate.evaluate (downshift pointer count, written) = _
          rw [ShiftSimulation.evaluateDownshift count pointer written _ writtenPointer]
          simp only [BitVec.add_sub_cancel]
          have restore : StackSemStateOps.setVar pointer (.word pointerWord) shifted = target := by
            dsimp [shifted]
            rw [StackFreeSimulation.setVarTwice, StackFreeSimulation.setVarExisting target pointer (.word pointerWord) pointerLookup]
          let newMemory : BitVec width → WordLocW width :=
            fun key => if key = (pointerWord + wordOffset count + 0) then value else target.memory key
          change (none, {(StackSemStateOps.setVar pointer (.word pointerWord) shifted) with memory := newMemory}) = _
          rw [restore]
          simp [updated, newMemory]
      · simpa only [updated, relation.1, Nat.add_comm] using
          StackHeapWrites.stateRelStackStore jump bounds pointer count source target source.stack pointerWord
            (pointerWord + wordOffset count) value
            ⟨relation, rfl, pointerLookup, safe, by rw [WordAddressArithmetic.wordOffsetEq]⟩
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectStackLoad
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectStackStore
