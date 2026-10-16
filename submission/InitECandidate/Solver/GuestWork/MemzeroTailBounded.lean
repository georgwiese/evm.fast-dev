import InitECandidate.Solver.GuestWork.MemzeroTailClock
import InitECandidate.Solver.FlattenWeighted.ClockAgreement

namespace InitECandidate.Solver.GuestWork.MemzeroTail
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Solver.FlattenWeighted

/-- Every non-timeout run of the actual byte tail has an equivalent execution
at the explicit clock budget, preserving result and the entire final state
apart from unused clock (in particular registers, memory and FFI). -/
theorem bounded_execution {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (base length index : BitVec 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index))
    (execution : evaluate (.loop body, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (.loop body, {source with clock := clockBudget length index}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work (.loop body) {source with clock := clockBudget length index}
        ((length.toNat - index.toNat + 1) * 29) := by
  have enough := enough_clock source base length index hbase hlength hindex
  rcases boundedRun : evaluate (.loop body, {source with clock := clockBudget length index}) with
    ⟨boundedResult, boundedPost⟩
  rw [boundedRun] at enough
  obtain ⟨sameResult, sameState⟩ := reclockAgreement (.loop body) source (clockBudget length index)
    result boundedResult post boundedPost execution boundedRun notTimeout enough
  refine ⟨boundedPost, ?_, sameState.symm, loop_work _ base length index hbase hlength hindex⟩
  simpa only [sameResult] using boundedRun

end InitECandidate.Solver.GuestWork.MemzeroTail
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.bounded_execution
