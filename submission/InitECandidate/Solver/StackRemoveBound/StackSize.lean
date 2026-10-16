import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackSize

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackSize
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

theorem compCorrectStackGetSize {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackGetSize register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackGetSize register : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackGetSize register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackGetSize] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  have resultEq := (Prod.mk.inj sourceRun).1.symm
  have sourceEq := (Prod.mk.inj sourceRun).2.symm
  subst result
  subst postSource
  obtain ⟨base, pointerLookup, baseLookup, inverse⟩ := sizeInverse jump bounds pointer source target relation
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, StackSemStateOps.setVar register (.word (BitVec.ofNat width source.stackSpace)) target, Nat.zero_le _, ?_, ?_⟩
  · simp only [Nat.zero_add]
    have execution := runGetSize target register pointer _ base pointerLookup baseLookup (by omega) good
    simpa only [comp, inverse] using execution
  · exact StateUpdates.stateRelSetVar jump bounds pointer register _ source target ⟨relation, lower⟩

/-- Full relation reconstructed after setting the stack position. This is
source-local constructor factoring, with no standalone HOL declaration. -/
theorem stateRelSizeStep {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (safe : count ≤ source.stack.length) :
    ∃ base : BitVec width,
      StackSemStateOps.getVar (pointer + 1) target = some (.word base) ∧
      stateRelHOL jump bounds pointer {source with stackSpace := count}
        (StackSemStateOps.setVar pointer (.word (base + bytesInWord width * BitVec.ofNat width count)) target) := by
  obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  refine ⟨base, baseLookup, ?_⟩
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  have baseNe : pointer + 1 ≠ pointer := by omega
  have heapNe : pointer + 2 ≠ pointer := by omega
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have low : ∀ query, query < pointer →
      (target.regs.updateEq (pointer, .word (base + bytesInWord width * BitVec.ofNat width count))).lookup query = source.regs.lookup query := by
    intro query below
    have ne : query ≠ pointer := by omega
    simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne, ite_false] using h18 query below
  simp only [stateRelHOL, StackSemStateOps.setVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, baseNe, heapNe, ite_false, ite_true, baseLookup]
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,low,h19,h20,h21,h22,h23,safe,
    h25.1,reserve,upper,True.intro,heap⟩

/-- Native SetSize executes the original shift and pointer reconstruction.
Lookup premises are supplied from the full source relation in the case below. -/
theorem runSetSize {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (word base : BitVec width)
    (wordLookup : state.regs.lookup register = some (.word word))
    (baseLookup : state.regs.lookup (pointer + 1) = some (.word base))
    (lower : register < pointer)
    (good : goodDimindex width) :
    StackSemEvaluate.evaluate (comp false (0,0) pointer (.stackSetSize register), state) =
      (none, StackSemStateOps.setVar pointer (.word (base + (word <<< wordShiftAmount width)))
        (StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) state)) := by
  have shiftBound : wordShiftAmount width < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftWidth : wordShiftAmount width < width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftRun : StackSemEvaluate.evaluate (leftShiftInst register (wordShiftAmount width), state) =
      (none, StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) state) := by
    simp [leftShiftInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, wordLookup, wordShiftHOL,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt shiftBound, Nat.not_le_of_gt shiftWidth]
  let shifted := StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) state
  have shiftedWord : shifted.regs.lookup register = some (.word (word <<< wordShiftAmount width)) := by
    simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have shiftedBase : shifted.regs.lookup (pointer + 1) = some (.word base) := by
    have different : pointer + 1 ≠ register := by omega
    simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different, baseLookup]
  rw [comp, StackSemEvaluate.evaluate_seq, shiftRun]
  simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
  change StackSemEvaluate.evaluate (.seq (moveInst pointer (pointer + 1)) (addInst pointer register), shifted) = _
  exact CompCorrect.StackMemoryAny.runMoveAdd shifted pointer (pointer + 1) register base (word <<< wordShiftAmount width) shiftedBase shiftedWord (by omega)
/-- Canonical updates to distinct registers commute. Flapjack infrastructure,
not a standalone HOL port. -/
theorem setVarCommute {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (first second : Nat)
    (a b : WordLocW width) (different : first ≠ second) :
    StackSemStateOps.setVar first a (StackSemStateOps.setVar second b state) =
      StackSemStateOps.setVar second b (StackSemStateOps.setVar first a state) := by
  have maps : (state.regs.updateEq (second,b)).updateEq (first,a) =
      (state.regs.updateEq (first,a)).updateEq (second,b) := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases eqFirst : query = first
    · subst query; simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different]
    · by_cases eqSecond : query = second <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eqFirst, eqSecond, Ne.symm different]
  simp [StackSemStateOps.setVar, maps]
/-- Full original StackSetSize case, with precisely the original four premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackSetSize {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackSetSize register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackSetSize register : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackSetSize register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackSetSize] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun

  cases lookup : StackSemStateOps.getVar register source with
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
      by_cases outsideBounds : source.stack.length ≤ word.toNat
      · rw [if_pos outsideBounds] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      · rw [if_neg outsideBounds] at sourceRun
        have resultEq := (Prod.mk.inj sourceRun).1.symm
        have sourceEq := (Prod.mk.inj sourceRun).2.symm
        subst result
        subst postSource
        obtain ⟨base, baseLookup, postRelation⟩ := stateRelSizeStep jump bounds pointer word.toNat source target
          relation (by omega)
        have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have targetLookup : target.regs.lookup register = some (.word word) := by
          change StackSemStateOps.getVar register target = some (.word word)
          rw [← RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower⟩]
          exact lookup
        have shiftEq : word <<< wordShiftAmount width = bytesInWord width * BitVec.ofNat width word.toNat := by
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, WordAddressArithmetic.lslWordShift word good, BitVec.mul_comm]
        let pointerTarget := StackSemStateOps.setVar pointer (.word (base + bytesInWord width * BitVec.ofNat width word.toNat)) target
        refine ⟨0, StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) pointerTarget, Nat.zero_le _, ?_, ?_⟩
        · simp only [Nat.zero_add]
          have execution := runSetSize target register pointer word base targetLookup baseLookup lower good
          rw [setVarCommute target pointer register _ _ (by omega), shiftEq] at execution
          simpa only [comp, pointerTarget, shiftEq] using execution
        · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register (.word (word <<< wordShiftAmount width)) {source with stackSpace := word.toNat}
            pointerTarget ⟨postRelation, lower⟩
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectStackGetSize
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectStackSetSize
