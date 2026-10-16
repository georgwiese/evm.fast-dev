import InitECandidate.Solver.FlattenBound.Common
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Guarded

/-! These constructors cannot produce a non-error result under the original
flattening state relation. Preserve that exact contradiction, with no cost guess. -/
namespace InitECandidate.Solver.FlattenBound
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
section
variable {width : Nat} [NeZero width] {C F : Type} (limit : Nat)

/-- Shared shape: the clause returns `SOME Error` from the state relation. -/
private theorem guarded {prog : HolProg width} {s1 : StackSemStateFiniteExact width C F}
    (h : ∀ (t : Flapjack.Compiler.Backend.LabSem.State width C F), stateRel s1 t →
      (StackSemEvaluate.evaluate (prog, s1)).1 = some .error) :
    BoundedProp limit prog s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -⟩
  have := h t1 rel
  rw [ev] at this
  exact absurd this nerr

theorem flattenCorrectAlloc (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedProp limit (.alloc k : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_alloc]; simp [(relNoStack rel).2.2]

theorem flattenCorrectStoreConsts (s1 : StackSemStateFiniteExact width C F)
    (a b : Nat) (stub : Option Nat) :
    BoundedProp limit (.storeConsts a b stub : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_storeConsts]; simp [(relNoStack rel).2.1]

theorem flattenCorrectGet (s1 : StackSemStateFiniteExact width C F) (v : Nat)
    (name : StoreName) : BoundedProp limit (.get v name : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_get]; simp [(relNoStack rel).2.1]

theorem flattenCorrectSet (s1 : StackSemStateFiniteExact width C F) (v : Nat)
    (name : StoreName) : BoundedProp limit (.set name v : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_set]; simp [(relNoStack rel).2.1]

theorem flattenCorrectOpCurrHeap (s1 : StackSemStateFiniteExact width C F)
    (op : Compiler.Encoders.Asm.HolBinop) (v src : Nat) :
    BoundedProp limit (.opCurrHeap op v src : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_opCurrHeap]; simp [(relNoStack rel).2.1]

theorem flattenCorrectStackAlloc (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedProp limit (.stackAlloc k : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_stackAlloc]; simp [(relNoStack rel).1]

theorem flattenCorrectStackFree (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedProp limit (.stackFree k : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_stackFree]; simp [(relNoStack rel).1]

theorem flattenCorrectStackLoad (s1 : StackSemStateFiniteExact width C F) (r k : Nat) :
    BoundedProp limit (.stackLoad r k : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_stackLoad]; simp [(relNoStack rel).1]

theorem flattenCorrectStackLoadAny (s1 : StackSemStateFiniteExact width C F) (r rn : Nat) :
    BoundedProp limit (.stackLoadAny r rn : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_stackLoadAny]; simp [(relNoStack rel).1]

theorem flattenCorrectStackStore (s1 : StackSemStateFiniteExact width C F) (r k : Nat) :
    BoundedProp limit (.stackStore r k : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_stackStore]; simp [(relNoStack rel).1]

theorem flattenCorrectStackStoreAny (s1 : StackSemStateFiniteExact width C F) (r rn : Nat) :
    BoundedProp limit (.stackStoreAny r rn : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_stackStoreAny]; simp [(relNoStack rel).1]

theorem flattenCorrectStackGetSize (s1 : StackSemStateFiniteExact width C F) (r : Nat) :
    BoundedProp limit (.stackGetSize r : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_stackGetSize]; simp [(relNoStack rel).1]

theorem flattenCorrectStackSetSize (s1 : StackSemStateFiniteExact width C F) (r : Nat) :
    BoundedProp limit (.stackSetSize r : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_stackSetSize]; simp [(relNoStack rel).1]

theorem flattenCorrectBitmapLoad (s1 : StackSemStateFiniteExact width C F) (r v : Nat) :
    BoundedProp limit (.bitmapLoad r v : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_bitmapLoad]; simp [(relNoStack rel).1]

theorem flattenCorrectDataBufferWrite (s1 : StackSemStateFiniteExact width C F) (r1 r2 : Nat) :
    BoundedProp limit (.dataBufferWrite r1 r2 : HolProg width) s1 :=
  guarded limit fun t rel => by
    rw [StackSemEvaluate.evaluate_dataBufferWrite]; simp [(relNoStack rel).1]

end
end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectAlloc
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectStoreConsts
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectGet
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectSet
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectOpCurrHeap
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectStackAlloc
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectStackFree
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectStackLoad
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectStackLoadAny
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectStackStore
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectStackStoreAny
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectStackGetSize
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectStackSetSize
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectBitmapLoad
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectDataBufferWrite
