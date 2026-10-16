import InitECandidate.Solver.GuestWork.ExtendMemoryTransfer

namespace InitECandidate.Solver.GuestWork.ExtendMemorySetup
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
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

/-- The actual capacity-call handler setup preserves its arguments and saved
logical length while reserving the 24-byte handler frame. Every failed setup
path is excluded by normal completion, rather than assumed valid. -/
theorem frame_setup {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (stack metadata : BitVec 64)
    (hstack : source.regs.lookup 24 = some (.word stack))
    (hmetadata : source.regs.lookup 25 = some (.word metadata))
    (separated : stack + 32#64 ≠ metadata + 18446744073709551560#64)
    (execution : evaluate (NamedBody484_183, source) = (none, post)) :
    post.code = source.code ∧ post.clock = source.clock ∧ post.mdomain = source.mdomain ∧
    post.regs.lookup 24 = some (.word (stack - 24#64)) ∧
    post.regs.lookup 25 = some (.word metadata) ∧
    post.regs.lookup 10 = source.regs.lookup 10 ∧ post.regs.lookup 11 = source.regs.lookup 11 ∧
    post.regs.lookup 26 = source.regs.lookup 26 ∧
    post.memory (stack + 32#64) = source.memory (stack + 32#64) := by
  have not0 : stack + 32#64 ≠ stack - 24#64 := by
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have not8 : stack + 32#64 ≠ stack - 24#64 + 8#64 := by
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have not16 : stack + 32#64 ≠ stack - 24#64 + 16#64 := by
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  by_cases lower : stack - 24#64 < metadata <;>
    by_cases label : StackSem.locCheckExact source.code (484, 5) <;>
    by_cases domain0 : source.mdomain (stack - 24#64) = true <;>
    by_cases domain8 : source.mdomain (stack - 24#64 + 8#64) = true <;>
    by_cases domain16 : source.mdomain (stack - 24#64 + 16#64) = true <;>
    by_cases domainMeta : source.mdomain (metadata + 18446744073709551560#64) = true
  all_goals
    simp [NamedBody484_155, NamedBody484_156, NamedBody484_157, NamedBody484_158, NamedBody484_159, NamedBody484_160, NamedBody484_161, NamedBody484_162, NamedBody484_163, NamedBody484_164, NamedBody484_165, NamedBody484_166, NamedBody484_167, NamedBody484_168, NamedBody484_169, NamedBody484_170, NamedBody484_171, NamedBody484_172, NamedBody484_173, NamedBody484_174, NamedBody484_175, NamedBody484_176, NamedBody484_177, NamedBody484_178, NamedBody484_179, NamedBody484_180, NamedBody484_181, NamedBody484_182, NamedBody484_183,
      seqEvaluate, evaluate_skip, evaluate_inst, evaluate_ite, evaluate_halt, evaluate_locValue,
      StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp, wordShiftHOL,
      memLoad, memStore, StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL,
      setVar, hstack, hmetadata, lower, label, domain0, domain8, domain16, domainMeta,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at execution
  all_goals
    subst post
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hmetadata, not0, not8, not16, separated]

end InitECandidate.Solver.GuestWork.ExtendMemorySetup
#print axioms InitECandidate.Solver.GuestWork.ExtendMemorySetup.frame_setup
