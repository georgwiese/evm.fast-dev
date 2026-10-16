import InitECandidate.Solver.GuestWork.GasAccounting
import InitECandidate.Solver.FlattenWeighted.ClockAgreement

namespace InitECandidate.Solver.GuestWork.GasAccounting
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted

/-- The actual affordable charge_gas path can be replayed with exactly two
initial Stack clock units and Work 49, preserving the result and every final
state field except unused clock. No claim is made about out-of-gas unwinding. -/
theorem bounded_charge {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (metadata offset heap globals frame gas used amount : BitVec 64) (returnLabel returnOffset : Nat)
    (ready : Ready source metadata offset heap globals frame gas used amount returnLabel returnOffset)
    (affordable : amount ≤ gas)
    (execution : evaluate (Named472.2, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (Named472.2, {source with clock := 2}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work Named472.2 {source with clock := 2} 49 := by
  rcases nextRun : evaluate (Named472.2, {source with clock := 2}) with ⟨nextResult, nextPost⟩
  have nextUpdate := ChargeGasEntry.updates {source with clock := 2} nextPost nextResult
    metadata offset heap globals frame gas used amount returnLabel returnOffset
    ready.metadataReg ready.heapReg ready.amountReg ready.metadataDomain ready.metadataValue
    ready.globalsEq ready.gasValue affordable ready.returnReg ready.globalDomain
    ready.gasDomain ready.usedDomain ready.globalValue ready.usedValue ready.globalNotGas
    ready.globalNotUsed (by exact Nat.le_refl 2) nextRun
  have nextNotTimeout : nextResult ≠ some .timeOut := by rw [nextUpdate.1]; simp
  obtain ⟨sameResult, sameState⟩ := reclockAgreement Named472.2 source 2
    result nextResult post nextPost execution nextRun notTimeout nextNotTimeout
  refine ⟨nextPost, ?_, sameState.symm, ?_⟩
  · simpa only [sameResult] using nextRun
  · exact ChargeGasEntry.work {source with clock := 2} metadata offset heap globals frame gas amount
      ready.metadataReg ready.heapReg ready.amountReg ready.metadataDomain ready.metadataValue
      ready.globalsEq ready.globalDomain ready.globalValue ready.gasDomain ready.gasValue affordable

end InitECandidate.Solver.GuestWork.GasAccounting
#print axioms InitECandidate.Solver.GuestWork.GasAccounting.bounded_charge
