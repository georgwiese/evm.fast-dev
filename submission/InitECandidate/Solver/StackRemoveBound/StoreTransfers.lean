import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StoreTransfers

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreTransfers
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

theorem compCorrectGet {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat) (name : StoreName)
    (hypothesis : StackSemEvaluate.evaluate (.get register name, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.get register name : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.get register name),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  rw [StackSemEvaluate.evaluate_get] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases lookup : source.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [lookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, StackSemStateOps.setVar register value target, Nat.zero_le _, ?_, ?_⟩
    · by_cases current : name = .currHeap
      · subst name
        have heapLookup := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [StackSemRegisterTransfers.storeOfSyntax] at lookup
        rw [lookup] at heapLookup
        simp [comp, moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
          StackSemIntegerInstructions.instInteger, heapLookup]
      · have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        dsimp only at heaps
        cases baseLookup : target.regs.lookup (pointer + 1) with
        | none => simp only [baseLookup] at heaps; exact heaps.2.elim
        | some baseValue =>
          cases baseValue with
          | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
          | word base =>
            simp only [baseLookup] at heaps
            have load := StoreHeapReads.memLoadLemma name source target value base
              ⟨StoreNames.nameCases name current, lookup, by
                simpa only [List.length_append, Nat.add_comm] using heaps.2.2.2.2⟩
            have expression : StackSemExpressions.wordExp target
                (.op .add [.var (pointer + 1), .const (storeOffset name)]) =
                some (base + storeOffset name) := by
              simp [StackSemExpressions.wordExp, baseLookup, wordOpHOL, wordOp]
            simp [comp, current, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
              StackSemIntegerInstructions.instInteger, expression, load]
    · exact StateUpdates.stateRelSetVar jump bounds pointer register value source target
        ⟨relation, bound⟩

/-- Full genuine Set case: the original bound excludes BitmapBase. CurrHeap
updates the reserved target register; every other name uses the full native
store heap write law. Target execution and all post-state relation conjuncts
are derived. The total evaluator retains inherited reals_as_rational_cuts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSet {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat) (name : StoreName)
    (hypothesis : StackSemEvaluate.evaluate (.set name register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.set name register : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ resultBudget result ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.set name register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  rw [StackSemEvaluate.evaluate_set] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases lookup : StackSemStateOps.getVar register source with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [lookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have getVarEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
      ⟨relation, bound.1⟩
    have targetLookup : target.regs.lookup register = some value := by
      simpa only [StackSemStateOps.getVar] using getVarEq.symm.trans lookup
    by_cases current : name = .currHeap
    · subst name
      refine ⟨0, StackSemStateOps.setVar (pointer + 2) value target, Nat.zero_le _, ?_, ?_⟩
      · simp [comp, moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
          StackSemIntegerInstructions.instInteger, targetLookup]
      · exact stateRelSetCurrHeap jump bounds pointer value source target relation
    · have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      dsimp only at heaps
      cases baseLookup : target.regs.lookup (pointer + 1) with
      | none => simp only [baseLookup] at heaps; exact heaps.2.elim
      | some baseValue =>
        cases baseValue with
        | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
        | word base =>
          simp only [baseLookup] at heaps
          have domain := StoreHeapReads.memLoadLemma2 name source target base
            ⟨StoreNames.nameCases name current, by
              simpa only [List.length_append, Nat.add_comm] using heaps.2.2.2.2⟩
          have expression : StackSemExpressions.wordExp target
              (.op .add [.var (pointer + 1), .const (storeOffset name)]) =
              some (base + storeOffset name) := by
            simp [StackSemExpressions.wordExp, baseLookup, wordOpHOL, wordOp]
          refine ⟨0, {target with memory := fun key =>
            if key = base + storeOffset name then value else target.memory key}, Nat.zero_le _, ?_, ?_⟩
          · simp [comp, current, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
              StackSemIntegerInstructions.instInteger, expression, StackSemStateOps.getVar,
              targetLookup, StackSemStateOps.memStore, domain]
          · exact stateRelSetStore jump bounds pointer name value base source target
              current bound.2 baseLookup relation

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectGet
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectSet
