import InitECandidate.Solver.GuestWork.FrameAllocCost
import InitECandidate.Solver.FlattenWeighted.ClockAgreement

namespace InitECandidate.Solver.GuestWork.FrameAllocEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted

/-- Concrete successful-path ABI, domains and guard facts. Establishing these
at every guest call remains a separate global invariant obligation. -/
structure Ready {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat) : Prop where
  hmetadata : source.regs.lookup 25 = some (.word metadata)
  hheap : source.regs.lookup 26 = some (.word heap)
  hstack : source.regs.lookup 24 = some (.word stack)
  hamount : source.regs.lookup 10 = some (.word amount)
  hreturn : source.regs.lookup 1 = some (.loc returnLabel returnOffset)
  stackSafe : ¬ stack - 32#64 < metadata
  metadataDomain : source.mdomain (metadata + 18446744073709551592#64) = true
  metadataValue : source.memory (metadata + 18446744073709551592#64) = .word offset
  globalsEq : (offset <<< (1 : Nat)) + heap = globals
  pointerDomain : source.mdomain (globals + 18446744073709551584#64) = true
  pointerValue : source.memory (globals + 18446744073709551584#64) = .word pointer
  scratchDomain : source.mdomain (globals + 18446744073709551592#64) = true
  scratchValue : source.memory (globals + 18446744073709551592#64) = .word scratch
  saveDomain : source.mdomain (stack - 32#64 + 24#64) = true
  metadataNotSave : metadata + 18446744073709551592#64 ≠ stack - 32#64 + 24#64
  scratchNotSave : globals + 18446744073709551592#64 ≠ stack - 32#64 + 24#64
  fits : ¬ scratch - pointer < amount
  roundedFits : ¬ scratch < ((amount + pointer + 7#64) &&& 18446744073709551608#64)

/-- Replay the actual successful allocator with four initial Stack clock
units and Work 58, preserving all final state except unused clock. -/
theorem bounded_allocate {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (ready : Ready source metadata offset heap globals stack pointer scratch amount returnLabel returnOffset)
    (execution : evaluate (Named71.2, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (Named71.2, {source with clock := 4}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work Named71.2 {source with clock := 4} 58 := by
  rcases nextRun : evaluate (Named71.2, {source with clock := 4}) with ⟨nextResult, nextPost⟩
  have nextUpdate := updates {source with clock := 4} nextPost nextResult
    metadata offset heap globals stack pointer scratch amount returnLabel returnOffset
    ready.hmetadata ready.hheap ready.hstack ready.hamount ready.hreturn ready.stackSafe ready.metadataDomain ready.metadataValue ready.globalsEq ready.pointerDomain ready.pointerValue ready.scratchDomain ready.scratchValue ready.saveDomain ready.metadataNotSave ready.scratchNotSave ready.fits ready.roundedFits
    (by exact Nat.le_refl 4) nextRun
  have nextNotTimeout : nextResult ≠ some .timeOut := by rw [nextUpdate.1]; simp
  obtain ⟨sameResult, sameState⟩ := reclockAgreement Named71.2 source 4
    result nextResult post nextPost execution nextRun notTimeout nextNotTimeout
  refine ⟨nextPost, ?_, sameState.symm, ?_⟩
  · simpa only [sameResult] using nextRun
  · exact work {source with clock := 4}
      metadata offset heap globals stack pointer scratch amount returnLabel returnOffset
      ready.hmetadata ready.hheap ready.hstack ready.hamount ready.hreturn ready.stackSafe ready.metadataDomain ready.metadataValue ready.globalsEq ready.pointerDomain ready.pointerValue ready.scratchDomain ready.scratchValue ready.saveDomain ready.metadataNotSave ready.scratchNotSave ready.fits ready.roundedFits
      (by exact Nat.le_refl 4)

end InitECandidate.Solver.GuestWork.FrameAllocEntry
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.bounded_allocate
