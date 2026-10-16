import InitECandidate.Solver.GuestWork.FrameAllocCall

namespace InitECandidate.Solver.GuestWork.ExtendMemoryAllocRestore
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

private theorem seqEvaluate {C F : Type} (p q : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

/-- The actual allocator return continuation restores capacity/next-capacity,
shifts the saved logical extension into its next slot, and preserves every
memory address outside its four writes. Failed domains cannot complete normally. -/
theorem restore {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F)
    (stack metadata capacity nextCapacity expansion : BitVec 64)
    (hstack : source.regs.lookup 24 = some (.word stack))
    (hmetadata : source.regs.lookup 25 = some (.word metadata))
    (savedCapacity : source.memory (stack + 24#64 + 40#64) = .word capacity)
    (savedNext : source.memory (stack + 24#64 + 8#64) = .word nextCapacity)
    (savedExpansion : source.memory (stack + 24#64 + 24#64) = .word expansion)
    (separateCapacity : stack + 24#64 + 40#64 ≠ metadata + 18446744073709551560#64)
    (separateNext : stack + 24#64 + 8#64 ≠ metadata + 18446744073709551560#64)
    (separateExpansion : stack + 24#64 + 24#64 ≠ metadata + 18446744073709551560#64)
    (run : evaluate (NamedBody484_116, source) = (none, post)) :
    post.code = source.code ∧ post.mdomain = source.mdomain ∧
    post.regs.lookup 24 = some (.word (stack + 24#64)) ∧
    post.regs.lookup 25 = some (.word metadata) ∧
    post.regs.lookup 26 = source.regs.lookup 26 ∧
    post.regs.lookup 11 = some (.word capacity) ∧
    post.regs.lookup 1 = some (.word nextCapacity) ∧
    post.memory (stack + 24#64 + 32#64) = .word expansion ∧
    (∀ address, address ≠ metadata + 18446744073709551560#64 →
      address ≠ stack + 24#64 + 40#64 → address ≠ stack + 24#64 + 32#64 →
      address ≠ stack + 24#64 + 24#64 → post.memory address = source.memory address) := by
  by_cases domain0 : source.mdomain (stack + 16#64) = true <;>
    by_cases domain1 : source.mdomain (metadata + 18446744073709551560#64) = true <;>
    by_cases domain2 : source.mdomain (stack + 24#64 + 40#64) = true <;>
    by_cases domain3 : source.mdomain (stack + 24#64 + 32#64) = true <;>
    by_cases domain4 : source.mdomain (stack + 24#64 + 24#64) = true <;>
    by_cases domain5 : source.mdomain (stack + 24#64 + 16#64) = true <;>
    by_cases domain6 : source.mdomain (stack + 24#64 + 8#64) = true
  all_goals
    simp [NamedBody484_94, NamedBody484_95, NamedBody484_96, NamedBody484_97, NamedBody484_98, NamedBody484_99, NamedBody484_100, NamedBody484_101, NamedBody484_102, NamedBody484_103, NamedBody484_104, NamedBody484_105, NamedBody484_106, NamedBody484_107, NamedBody484_108, NamedBody484_109, NamedBody484_110, NamedBody484_111, NamedBody484_112, NamedBody484_113, NamedBody484_114, NamedBody484_115, NamedBody484_116,
      seqEvaluate, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger,
      assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, StackSemStateOps.getVar, setVar,
      hstack, hmetadata, savedCapacity, savedNext, savedExpansion,
      separateCapacity, separateNext, separateExpansion,
      domain0, domain1, domain2, domain3, domain4, domain5, domain6,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run
  all_goals
    subst post
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hmetadata,
      savedCapacity, savedNext, savedExpansion, separateCapacity, separateNext, separateExpansion]
    intro address notMeta notCapacity notLength notNextLength
    simp [notMeta, notCapacity, notLength, notNextLength]

end InitECandidate.Solver.GuestWork.ExtendMemoryAllocRestore
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryAllocRestore.restore
