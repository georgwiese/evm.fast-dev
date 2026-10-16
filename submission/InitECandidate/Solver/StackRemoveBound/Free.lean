import Flapjack.Compiler.Backend.StackRemove.Proofs.StackFreeSimulation

/-! Arbitrary-count stack release preserves the zero-extra-clock witness. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.StackFreeSimulation

theorem evaluateStackFree {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target) :
    ∃ clock postTarget, clock = 0 ∧
      StackSemEvaluate.evaluate (stackFree pointer count,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨sourceRun, notError, relation⟩
  rw [StackSemEvaluate.evaluate_stackFree] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases safe : source.stack.length < source.stackSpace + count
  · rw [if_pos safe] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · rw [if_neg safe] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨base, _baseLookup, _lower, _upper, pointerLookup, _heap⟩ :=
      StackPointer.stateRelGetVarK jump bounds pointer source target relation
    have lookup : target.regs.lookup pointer =
        some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := pointerLookup
    refine ⟨0, StackSemStateOps.setVar pointer
      (.word ((base + bytesInWord width * BitVec.ofNat width source.stackSpace) + wordOffset count)) target, rfl, ?_, ?_⟩
    · simpa only [Nat.zero_add] using runFree count pointer target _ lookup
    · simpa only [lookup, relation.1] using stateRelFreeStep jump bounds pointer count source target relation (Nat.le_of_not_gt safe)
end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.evaluateStackFree
