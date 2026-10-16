import Flapjack.Compiler.Backend.StackRemove.Proofs.StackAllocSimulation

/-! Stack removal's arbitrary-count allocation needs at most one extra source
clock. Successful chunks use none; an overflow terminates at the first failing
chunk. The full original state relation and overflow guards are retained. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.StackAllocSimulation

theorem evaluateSingleStackAlloc {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      (result, postSource) = (if source.stackSpace < count then
        (some (.halt (.word 2)), StackSemStateOps.emptyEnv source)
        else (none, {source with stackSpace := source.stackSpace - count})) ∧
      count ≠ 0 ∧ count ≤ maxStackAlloc) :
    ∃ clock postTarget, clock ≤ 1 ∧ (count ≤ source.stackSpace → clock = 0) ∧
      StackSemEvaluate.evaluate (singleStackAlloc jump pointer count,
        {target with clock := target.clock + clock}) = (result, postTarget) ∧
      (if source.stackSpace < count then postTarget.ffi = postSource.ffi
       else stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨relation, output, _nonzero, countBound⟩
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, _heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spaceBound : source.stackSpace ≤ source.stack.length := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have comparison := AllocationArithmetic.allocationGuard base source.stackSpace source.stack.length count good lower upper spaceBound countBound
  have guard : Compiler.Encoders.Asm.wordCmpHOL .lower
      (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count) base =
      decide (source.stackSpace < count) := by
    simp only [Compiler.Encoders.Asm.wordCmpHOL, comparison]
  have codeLookup : sptLookup stackErrLab target.code = some (haltInst (BitVec.ofNat width 2)) := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have baseNe : pointer + 1 ≠ pointer := by omega
  by_cases overflow : source.stackSpace < count
  · rw [if_pos overflow] at output
    rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    simp only [overflow, decide_true] at guard
    cases jump with
    | false =>
      refine ⟨1, StackSemStateOps.emptyEnv {target with clock := target.clock + 1}, Nat.le_refl _, (by intro available; omega), ?_, ?_⟩
      · simp [singleStackAlloc,  StackSemStateOps.emptyEnv, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
          StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup,
          wordOpHOL, wordOp, StackSemControl.fixClock,
          StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          StackSemEvaluate.evaluate_ite,
          StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm,
          wordSemWordCmp, baseLookup, guard,
            haltInst,
          StackSemEvaluate.evaluate_halt]
      · simpa [overflow, StackSemStateOps.emptyEnv] using relation.2.2.2.2.2.2.2.2.2.1
    | true =>
      refine ⟨1, StackSemStateOps.emptyEnv target, Nat.le_refl _, (by intro available; omega), ?_, ?_⟩
      · simp [singleStackAlloc,  StackSemStateOps.emptyEnv, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
          StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup,
          wordOpHOL, wordOp, StackSemControl.fixClock,
          StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
           StackSemEvaluate.evaluate_jumpLower,
          StackSemStateOps.getVar,
           baseLookup, guard,
          StackSemControl.findCode, codeLookup, haltInst,
          StackSemEvaluate.evaluate_halt, StackSemStateOps.decClock, StackSemControl.badFunReturn]
      · simpa [overflow, StackSemStateOps.emptyEnv] using relation.2.2.2.2.2.2.2.2.2.1
  · rw [if_neg overflow] at output
    rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, StackSemStateOps.setVar pointer
      (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count)) target, Nat.zero_le _, (by intro; rfl), ?_, ?_⟩
    · cases jump <;> simp [singleStackAlloc,  StackSemEvaluate.evaluate_seq,
        StackSemEvaluate.evaluate_inst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
        StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup, wordOpHOL, wordOp,
        StackSemControl.fixClock, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        StackSemEvaluate.evaluate_ite, StackSemEvaluate.evaluate_jumpLower, StackSemEvaluate.evaluate_skip,
        StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm, wordSemWordCmp, baseLookup, guard, overflow]
    · rw [if_neg overflow]
      simpa only [pointerLookup] using stateRelAllocStep jump bounds pointer count source target relation (Nat.le_of_not_gt overflow)
set_option maxRecDepth 2048 in
/-- Source-local strong-induction execution contract for the native recursive builder.
No standalone HOL declaration; this factors the original allocation proof. -/
theorem runAlloc {width : Nat} [NeZero width] {C F : Type}
    (count : Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    ∃ clock postTarget, clock ≤ 1 ∧ (count ≤ source.stackSpace → clock = 0) ∧
      StackSemEvaluate.evaluate (stackAlloc jump pointer count, {target with clock := clock + target.clock}) =
        ((if source.stackSpace < count then some (.halt (.word 2)) else none), postTarget) ∧
      (if source.stackSpace < count then postTarget.ffi = source.ffi
       else stateRelHOL jump bounds pointer {source with stackSpace := source.stackSpace - count} postTarget) := by
  classical
  induction count using Nat.strongRecOn generalizing source target with
  | ind count ih =>
    by_cases zero : count = 0
    · subst count
      exact ⟨0, target, Nat.zero_le _, (by intro; rfl), by simp [stackAlloc, StackSemEvaluate.evaluate_skip], by simpa using relation⟩
    by_cases small : count ≤ maxStackAlloc
    · let expectedSource := if source.stackSpace < count then StackSemStateOps.emptyEnv source
        else {source with stackSpace := source.stackSpace - count}
      obtain ⟨clock, postTarget, smallClock, zeroClock, run, post⟩ := evaluateSingleStackAlloc jump bounds pointer count
        source target expectedSource (if source.stackSpace < count then some (.halt (.word 2)) else none)
        ⟨relation, by dsimp [expectedSource]; split <;> rfl, zero, small⟩
      refine ⟨clock, postTarget, smallClock, zeroClock, ?_, ?_⟩
      · rw [stackAlloc, if_neg zero, if_pos small]
        simpa only [Nat.add_comm] using run
      · by_cases overflow : source.stackSpace < count
        · simpa [overflow, expectedSource, StackSemStateOps.emptyEnv] using post
        · simpa [overflow, expectedSource] using post
    by_cases firstOverflow : source.stackSpace < maxStackAlloc
    · have overflow : source.stackSpace < count := by omega
      obtain ⟨clock, postTarget, smallClock, zeroClock, run, post⟩ := evaluateSingleStackAlloc jump bounds pointer maxStackAlloc
        source target (StackSemStateOps.emptyEnv source) (some (.halt (.word 2)))
        ⟨relation, by rw [if_pos firstOverflow], by decide, Nat.le_refl _⟩
      have firstRun : StackSemEvaluate.evaluate (singleStackAlloc jump pointer maxStackAlloc,
          {target with clock := clock + target.clock}) = (some (.halt (.word 2)),postTarget) := by
        simpa only [Nat.add_comm] using run
      refine ⟨clock, (StackSemControl.fixClock {target with clock := clock + target.clock}
        ((some (.halt (.word 2)) : Option (StackSemResult width)), postTarget)).2, smallClock, (by intro enough; omega), ?_, ?_⟩
      · rw [stackAlloc, if_neg zero, if_neg small, StackSemEvaluate.evaluate_seq, firstRun]
        simp [StackSemControl.fixClock, overflow]
      · simpa [overflow, firstOverflow, StackSemControl.fixClock, StackSemStateOps.emptyEnv] using post
    · have available : maxStackAlloc ≤ source.stackSpace := Nat.le_of_not_gt firstOverflow
      let nextSource := {source with stackSpace := source.stackSpace - maxStackAlloc}
      let nextTarget := StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word word) => word | _ => 0) - wordOffset maxStackAlloc)) target
      have nextRelation : stateRelHOL jump bounds pointer nextSource nextTarget :=
        stateRelAllocStep jump bounds pointer maxStackAlloc source target relation available
      obtain ⟨clock, postTarget, smallClock, zeroClock, run, post⟩ := ih (count - maxStackAlloc)
        (by simp only [maxStackAlloc] at *; omega) nextSource nextTarget nextRelation
      have overflowEq : nextSource.stackSpace < count - maxStackAlloc ↔ source.stackSpace < count := by
        dsimp [nextSource]; omega
      have subtractionEq : (source.stackSpace - maxStackAlloc) - (count - maxStackAlloc) = source.stackSpace - count := by omega
      refine ⟨clock, postTarget, smallClock, ?_, ?_, ?_⟩
      · intro enough
        apply zeroClock
        dsimp only [nextSource]
        omega
      · rw [stackAlloc, if_neg zero, if_neg small, StackSemEvaluate.evaluate_seq]
        have firstRun := runSingleAvailable jump bounds pointer maxStackAlloc (clock + target.clock)
          source target relation available (Nat.le_refl _)
        have presented : StackSemEvaluate.evaluate (singleStackAlloc jump pointer maxStackAlloc,
          {target with clock := clock + target.clock}) = (none, {nextTarget with clock := clock + nextTarget.clock}) := by
          rw [firstRun]
          simp only [nextTarget, StackSemStateOps.setVar]
          cases found : target.regs.lookup pointer with
          | none => rfl
          | some value => cases value <;> rfl
        rw [presented]
        have clamp : StackSemControl.fixClock {target with clock := clock + target.clock}
            ((none : Option (StackSemResult width)), {nextTarget with clock := clock + nextTarget.clock}) =
            (none, {nextTarget with clock := clock + nextTarget.clock}) := by
          simp [StackSemControl.fixClock, nextTarget, StackSemStateOps.setVar]
        rw [clamp]
        simpa only [overflowEq] using run
      · simpa only [overflowEq, nextSource, subtractionEq] using post
attribute [local instance] Classical.propDecidable
/-- Full original arbitrary-count stack allocation simulation, including both
native overflow modes and the original universally quantified non-Halt branch. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackAlloc {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target) :
    ∃ clock postTarget, clock ≤ 1 ∧ (count ≤ source.stackSpace → clock = 0) ∧
      StackSemEvaluate.evaluate (stackAlloc jump pointer count,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (if ∀ word, result ≠ some (.halt word) then
        stateRelHOL jump bounds pointer postSource postTarget else postTarget.ffi = postSource.ffi) := by
  classical
  rcases hypothesis with ⟨sourceRun, _notError, relation⟩
  rw [StackSemEvaluate.evaluate_stackAlloc] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  obtain ⟨clock, postTarget, smallClock, zeroClock, targetRun, post⟩ := runAlloc count jump bounds pointer source target relation
  by_cases overflow : source.stackSpace < count
  · rw [if_pos overflow] at sourceRun targetRun post
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨clock, postTarget, smallClock, zeroClock, targetRun, ?_⟩
    simpa [StackSemStateOps.emptyEnv] using post
  · rw [if_neg overflow] at sourceRun targetRun post
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    exact ⟨clock, postTarget, smallClock, zeroClock, targetRun, by simpa [relation.1] using post⟩
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.evaluateSingleStackAlloc
#print axioms InitECandidate.Solver.StackRemoveBound.runAlloc
#print axioms InitECandidate.Solver.StackRemoveBound.evaluateStackAlloc
