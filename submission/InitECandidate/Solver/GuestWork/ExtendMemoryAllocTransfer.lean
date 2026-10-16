import InitECandidate.Solver.GuestWork.ExtendMemoryAllocRestore

namespace InitECandidate.Solver.GuestWork.ExtendMemoryAllocTransfer
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemControl
open InitECandidate.Proofs.BackendStages
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Normal completion of the actual call134 selects its real allocator return
and continuation116; all other callee outcomes stop the call. -/
theorem normal_returns {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F)
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (valid : FrameAllocCall.pre metadata offset heap globals stack pointer scratch amount 484 2 source)
    (execution : evaluate (NamedBody484_134, source) = (none, post)) :
    ∃ middle,
      evaluate (Named71.2, decClock (setVar 1 (.loc 484 2) source)) =
        (some (.result (.loc 484 2)), middle) ∧
      evaluate (NamedBody484_116, middle) = (none, post) := by
  rw [NamedBody484_134, evaluate_call] at execution
  simp only [findCode, valid.1] at execution
  by_cases zero : source.clock = 0
  · simp [zero] at execution
  simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
  rcases run : evaluate (Named71.2, decClock (setVar 1 (.loc 484 2) source)) with ⟨result, middle⟩
  rw [run] at execution
  have choices := FrameAllocEntry.outcome _ middle result metadata offset heap globals stack pointer scratch amount
    484 2 valid.2 run
  rcases choices with returned | ⟨timedOut, _⟩
  · refine ⟨middle, ?_, ?_⟩
    · simpa only [returned] using run
    · simpa only [returned, ne_eq, not_true_eq_false, if_false] using execution
  · simp [timedOut] at execution

/-- Saved-state transfer across actual allocator call134, its callee and its
return continuation. Memory is unchanged outside the allocator and restore
write locations; the saved expansion moves to its capacity-call slot. -/
theorem saved_state {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F)
    (metadata offset heap globals stack pointer scratch amount capacity nextCapacity expansion : BitVec 64)
    (valid : FrameAllocCall.pre metadata offset heap globals stack pointer scratch amount 484 2 source)
    (savedCapacity : source.memory (stack + 24#64 + 40#64) = .word capacity)
    (savedNext : source.memory (stack + 24#64 + 8#64) = .word nextCapacity)
    (savedExpansion : source.memory (stack + 24#64 + 24#64) = .word expansion)
    (capacityNotPointer : stack + 24#64 + 40#64 ≠ globals + 18446744073709551584#64)
    (nextNotPointer : stack + 24#64 + 8#64 ≠ globals + 18446744073709551584#64)
    (expansionNotPointer : stack + 24#64 + 24#64 ≠ globals + 18446744073709551584#64)
    (capacityNotMeta : stack + 24#64 + 40#64 ≠ metadata + 18446744073709551560#64)
    (nextNotMeta : stack + 24#64 + 8#64 ≠ metadata + 18446744073709551560#64)
    (expansionNotMeta : stack + 24#64 + 24#64 ≠ metadata + 18446744073709551560#64)
    (execution : evaluate (NamedBody484_134, source) = (none, post)) :
    post.code = source.code ∧ post.mdomain = source.mdomain ∧
    post.regs.lookup 24 = some (.word (stack + 24#64)) ∧
    post.regs.lookup 25 = some (.word metadata) ∧
    post.regs.lookup 26 = source.regs.lookup 26 ∧
    post.regs.lookup 11 = some (.word capacity) ∧
    post.regs.lookup 1 = some (.word nextCapacity) ∧
    post.memory (stack + 24#64 + 32#64) = .word expansion ∧
    (∀ address, address ≠ globals + 18446744073709551584#64 →
      address ≠ stack - 32#64 + 24#64 → address ≠ metadata + 18446744073709551560#64 →
      address ≠ stack + 24#64 + 40#64 → address ≠ stack + 24#64 + 32#64 →
      address ≠ stack + 24#64 + 24#64 → post.memory address = source.memory address) := by
  obtain ⟨middle, calleeRun, restoreRun⟩ := normal_returns source post metadata offset heap globals
    stack pointer scratch amount valid execution
  let entered := decClock (setVar 1 (.loc 484 2) source)
  have ready : FrameAllocEntry.Ready entered metadata offset heap globals stack pointer scratch amount 484 2 := valid.2
  have enough : 4 ≤ entered.clock := by
    by_contra tooSmall
    have timedOut := FrameAllocEntry.small_timeout entered metadata offset heap globals stack pointer scratch amount
      484 2 ready (by omega)
    rw [calleeRun] at timedOut
    simp at timedOut
  have effects := FrameAllocEntry.updates entered middle (some (.result (.loc 484 2)))
    metadata offset heap globals stack pointer scratch amount 484 2 ready.hmetadata ready.hheap ready.hstack
    ready.hamount ready.hreturn ready.stackSafe ready.metadataDomain ready.metadataValue ready.globalsEq
    ready.pointerDomain ready.pointerValue ready.scratchDomain ready.scratchValue ready.saveDomain
    ready.metadataNotSave ready.scratchNotSave ready.fits ready.roundedFits enough calleeRun
  obtain ⟨_, _, _, _, domains, _, _, memory⟩ := effects
  have frame := FrameAllocEntry.preserved entered middle (some (.result (.loc 484 2)))
    metadata offset heap globals stack pointer scratch amount 484 2 ready calleeRun (by simp)
  have keepCapacity := memory (stack + 24#64 + 40#64) capacityNotPointer
    (by simp [BitVec.sub_eq_add_neg, BitVec.add_assoc])
  have keepNext := memory (stack + 24#64 + 8#64) nextNotPointer
    (by simp [BitVec.sub_eq_add_neg, BitVec.add_assoc])
  have keepExpansion := memory (stack + 24#64 + 24#64) expansionNotPointer
    (by simp [BitVec.sub_eq_add_neg, BitVec.add_assoc])
  have restored := ExtendMemoryAllocRestore.restore middle post stack metadata capacity nextCapacity expansion
    (frame.2.1.trans ready.hstack) (frame.2.2.1.trans ready.hmetadata)
    (keepCapacity.trans savedCapacity) (keepNext.trans savedNext) (keepExpansion.trans savedExpansion)
    capacityNotMeta nextNotMeta expansionNotMeta restoreRun
  obtain ⟨code, domain, hstack, hmetadata, hheap, hcapacity, hnext, hsaved, untouched⟩ := restored
  refine ⟨code.trans frame.1, domain.trans domains, hstack, hmetadata, ?_, hcapacity, hnext, hsaved, ?_⟩
  · simpa [entered, decClock, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using
      hheap.trans frame.2.2.2.1
  · intro address notPointer notSave notMeta notCapacity notLength notNextLength
    exact (untouched address notMeta notCapacity notLength notNextLength).trans
      (memory address notPointer notSave)

end InitECandidate.Solver.GuestWork.ExtendMemoryAllocTransfer
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryAllocTransfer.normal_returns
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryAllocTransfer.saved_state
