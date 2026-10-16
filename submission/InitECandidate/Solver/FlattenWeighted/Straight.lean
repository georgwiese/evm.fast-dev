import InitECandidate.Solver.FlattenBound.Assembly

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.FlattenBound

/-- Code that never enters another procedure or a recursive loop. -/
def straight {width : Nat} [NeZero width] : HolProg width → Bool
  | .seq first second | .ite _ _ _ first second => straight first && straight second
  | .call .. | .loop .. | .jumpLower .. | .rawCall .. | .install .. => false
  | _ => true

/-- Straight code has a bound independent of all installed procedure sizes.
The original flattening hypotheses and full result-dependent conclusion remain. -/
theorem straightBounded {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F)
    (supported : straight prog = true) : BoundedProp 0 prog s1 := by
  cases prog with
  | skip => exact flattenCorrectSkip 0 s1
  | inst i => exact flattenCorrectInst 0 s1 i
  | get v name => exact flattenCorrectGet 0 s1 v name
  | set name v => exact flattenCorrectSet 0 s1 v name
  | opCurrHeap op v src => exact flattenCorrectOpCurrHeap 0 s1 op v src
  | call ret dest handler =>
    simp [straight] at supported
  | seq c1 c2 =>
    have both : straight c1 = true ∧ straight c2 = true := by
      simpa only [straight, Bool.and_eq_true] using supported
    apply flattenCorrectSeq 0 s1 c1 c2
    · exact straightBounded c1 s1 both.1
    · intro middle execution
      exact straightBounded c2 middle both.2
  | ite cmp reg ri c1 c2 =>
    have both : straight c1 = true ∧ straight c2 = true := by
      simpa only [straight, Bool.and_eq_true] using supported
    exact flattenCorrectIf 0 s1 cmp reg ri c1 c2
      (straightBounded c1 s1 both.1) (straightBounded c2 s1 both.2)
  | loop body =>
    simp [straight] at supported
  | jumpLower r1 r2 dest =>
    simp [straight] at supported
  | alloc k => exact flattenCorrectAlloc 0 s1 k
  | storeConsts a b stub => exact flattenCorrectStoreConsts 0 s1 a b stub
  | raise v => exact flattenCorrectRaise 0 s1 v
  | ret v => exact flattenCorrectRet 0 s1 v
  | «break» k => exact flattenCorrectBreak 0 s1 k
  | «continue» k => exact flattenCorrectContinue 0 s1 k
  | ffi f ptr len ptr2 len2 ret => exact flattenCorrectFfi 0 s1 f ptr len ptr2 len2 ret
  | tick => exact flattenCorrectTick 0 s1
  | locValue reg l1 l2 => exact flattenCorrectLocValue 0 s1 reg l1 l2
  | install ptr len dptr dlen ret =>
    simp [straight] at supported
  | shMemOp op reg addr =>
    rcases addr with ⟨a, w⟩
    exact flattenCorrectShMemOp 0 s1 op reg a w
  | codeBufferWrite r1 r2 => exact flattenCorrectCodeBufferWrite 0 s1 r1 r2
  | dataBufferWrite r1 r2 => exact flattenCorrectDataBufferWrite 0 s1 r1 r2
  | rawCall dest =>
    simp [straight] at supported
  | stackAlloc k => exact flattenCorrectStackAlloc 0 s1 k
  | stackFree k => exact flattenCorrectStackFree 0 s1 k
  | stackStore r k => exact flattenCorrectStackStore 0 s1 r k
  | stackStoreAny r rn => exact flattenCorrectStackStoreAny 0 s1 r rn
  | stackLoad r k => exact flattenCorrectStackLoad 0 s1 r k
  | stackLoadAny r rn => exact flattenCorrectStackLoadAny 0 s1 r rn
  | stackGetSize r => exact flattenCorrectStackGetSize 0 s1 r
  | stackSetSize r => exact flattenCorrectStackSetSize 0 s1 r
  | bitmapLoad r v => exact flattenCorrectBitmapLoad 0 s1 r v
  | halt v => exact flattenCorrectHalt 0 s1 v
termination_by sizeOf prog

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.straightBounded
