import InitECandidate.Solver.FlattenBound.CallReturn
import InitECandidate.Solver.FlattenBound.RemainingLeaves
import InitECandidate.Solver.FlattenBound.Guarded
import InitECandidate.Solver.FlattenBound.ShMem
import InitECandidate.Solver.FlattenBound.Ffi
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

/-! Quantitative flattening for every installation-free Stack program whose
code and compile-oracle extensions satisfy the same finite syntax bound.
All cases preserve the original correctness preconditions and execution witness. -/
namespace InitECandidate.Solver.FlattenBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

/-- Close every constructor under the evaluator's original induction measure. -/
theorem boundedPropOfIH {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F)
    (ok : ProgramOk limit prog) (safe : StateOk limit s1)
    (ih : BoundedIH limit prog s1) : BoundedProp limit prog s1 := by
  have bodies : ∀ key p, sptLookup key s1.code = some p → nodes p ≤ limit :=
    fun key p lookup => (safe.1 key p lookup).1
  cases prog with
  | skip => exact flattenCorrectSkip limit s1
  | inst i => exact flattenCorrectInst limit s1 i
  | get v name => exact flattenCorrectGet limit s1 v name
  | set name v => exact flattenCorrectSet limit s1 v name
  | opCurrHeap op v src => exact flattenCorrectOpCurrHeap limit s1 op v src
  | call ret dest handler =>
    rcases ret with _ | ⟨rp, link, l1, l2⟩
    · apply flattenCorrectCallTail limit s1 dest handler bodies
      intro nonzero key p lookup
      exact ih p _ (.inl (by simp only [StackSemStateOps.decClock]; omega))
        (safe.1 key p lookup) safe
    · exact flattenCorrectCallRet limit s1 rp link l1 l2 dest handler safe ok ih
  | seq c1 c2 =>
    obtain ⟨ok1, ok2⟩ := programOk_seq limit c1 c2 ok
    apply flattenCorrectSeq limit s1 c1 c2
    · exact ih c1 s1 (.inr ⟨rfl, StackSemMeasure.seq_first_size_lt c1 c2⟩) ok1 safe
    · intro middle execution
      exact ih c2 middle
        (measureLtOfClockLe (StackSemEvaluateClock.evaluateClock _ _ _ _ execution)
          (StackSemMeasure.seq_second_size_lt c1 c2)) ok2
        (stateOk_evaluate limit c1 s1 middle none safe execution)
  | ite cmp reg ri c1 c2 =>
    obtain ⟨ok1, ok2⟩ := programOk_if limit cmp reg ri c1 c2 ok
    exact flattenCorrectIf limit s1 cmp reg ri c1 c2
      (ih c1 s1 (.inr ⟨rfl, StackSemMeasure.if_first_size_lt cmp reg ri c1 c2⟩) ok1 safe)
      (ih c2 s1 (.inr ⟨rfl, StackSemMeasure.if_second_size_lt cmp reg ri c1 c2⟩) ok2 safe)
  | loop body =>
    have bodyOk := programOk_loop limit body ok
    apply flattenCorrectLoop limit s1 body bodyOk.1
      (ih body s1 (.inr ⟨rfl, StackSemMeasure.loop_body_size_lt body⟩) bodyOk safe)
    intro post res execution _ nonzero
    have clock := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
    exact ih (.loop body) _ (.inl (by simp only [StackSemStateOps.decClock]; omega)) ok
      (stateOk_evaluate limit body s1 post res safe execution)
  | jumpLower r1 r2 dest =>
    apply flattenCorrectJumpLower limit s1 r1 r2 dest bodies
    intro nonzero key p lookup
    exact ih p _ (.inl (by simp only [StackSemStateOps.decClock]; omega))
      (safe.1 key p lookup) safe
  | alloc k => exact flattenCorrectAlloc limit s1 k
  | storeConsts a b stub => exact flattenCorrectStoreConsts limit s1 a b stub
  | raise v => exact flattenCorrectRaise limit s1 v
  | ret v => exact flattenCorrectRet limit s1 v
  | «break» k => exact flattenCorrectBreak limit s1 k
  | «continue» k => exact flattenCorrectContinue limit s1 k
  | ffi f ptr len ptr2 len2 ret => exact flattenCorrectFfi limit s1 f ptr len ptr2 len2 ret
  | tick => exact flattenCorrectTick limit s1
  | locValue reg l1 l2 => exact flattenCorrectLocValue limit s1 reg l1 l2
  | install ptr len dptr dlen ret =>
    have impossible := ok.2
    simp only [StackProps.noInstall, Bool.false_eq_true] at impossible
  | shMemOp op reg addr =>
    rcases addr with ⟨a, w⟩
    exact flattenCorrectShMemOp limit s1 op reg a w
  | codeBufferWrite r1 r2 => exact flattenCorrectCodeBufferWrite limit s1 r1 r2
  | dataBufferWrite r1 r2 => exact flattenCorrectDataBufferWrite limit s1 r1 r2
  | rawCall dest =>
    apply flattenCorrectRawCall limit s1 dest bodies
    intro nonzero prelude body lookup
    exact ih body _ (.inl (by simp only [StackSemStateOps.decClock]; omega))
      (programOk_seq limit prelude body (safe.1 dest _ lookup)).2 safe
  | stackAlloc k => exact flattenCorrectStackAlloc limit s1 k
  | stackFree k => exact flattenCorrectStackFree limit s1 k
  | stackStore r k => exact flattenCorrectStackStore limit s1 r k
  | stackStoreAny r rn => exact flattenCorrectStackStoreAny limit s1 r rn
  | stackLoad r k => exact flattenCorrectStackLoad limit s1 r k
  | stackLoadAny r rn => exact flattenCorrectStackLoadAny limit s1 r rn
  | stackGetSize r => exact flattenCorrectStackGetSize limit s1 r
  | stackSetSize r => exact flattenCorrectStackSetSize limit s1 r
  | bitmapLoad r v => exact flattenCorrectBitmapLoad limit s1 r v
  | halt v => exact flattenCorrectHalt limit s1 v

/-- Recursive clock-offset bound for the full Stack-to-Lab flattening pass. -/
theorem boundedPropAll {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F)
    (ok : ProgramOk limit prog) (safe : StateOk limit s1) : BoundedProp limit prog s1 :=
  (measureLtWf.induction
    (C := fun a => ProgramOk limit a.1 → StateOk limit a.2 → BoundedProp limit a.1 a.2)
    (prog, s1) fun a ih ok safe =>
      boundedPropOfIH limit a.1 a.2 ok safe fun p' s' less => ih (p', s') less) ok safe

end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.boundedPropOfIH
#print axioms InitECandidate.Solver.FlattenBound.boundedPropAll
