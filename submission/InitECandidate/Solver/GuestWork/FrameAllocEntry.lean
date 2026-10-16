import InitECandidate.Solver.FlattenWeighted.Work
import InitECandidate.Proofs.BackendStages.Named71

namespace InitECandidate.Solver.GuestWork.FrameAllocEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem seqEvaluate {C F : Type} (p q : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

/-- The actual successful frame-memory allocation path. The caller must supply
valid metadata, a safe stack frame, and both allocation guards. -/
theorem updates {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (hmetadata : source.regs.lookup 25 = some (.word metadata))
    (hheap : source.regs.lookup 26 = some (.word heap))
    (hstack : source.regs.lookup 24 = some (.word stack))
    (hamount : source.regs.lookup 10 = some (.word amount))
    (hreturn : source.regs.lookup 1 = some (.loc returnLabel returnOffset))
    (stackSafe : ¬ stack - 32#64 < metadata)
    (metadataDomain : source.mdomain (metadata + 18446744073709551592#64) = true)
    (metadataValue : source.memory (metadata + 18446744073709551592#64) = .word offset)
    (globalsEq : (offset <<< (1 : Nat)) + heap = globals)
    (pointerDomain : source.mdomain (globals + 18446744073709551584#64) = true)
    (pointerValue : source.memory (globals + 18446744073709551584#64) = .word pointer)
    (scratchDomain : source.mdomain (globals + 18446744073709551592#64) = true)
    (scratchValue : source.memory (globals + 18446744073709551592#64) = .word scratch)
    (saveDomain : source.mdomain (stack - 32#64 + 24#64) = true)
    (metadataNotSave : metadata + 18446744073709551592#64 ≠ stack - 32#64 + 24#64)
    (scratchNotSave : globals + 18446744073709551592#64 ≠ stack - 32#64 + 24#64)
    (fits : ¬ scratch - pointer < amount)
    (roundedFits : ¬ scratch < ((amount + pointer + 7#64) &&& 18446744073709551608#64))
    (enoughClock : 4 ≤ source.clock)
    (execution : evaluate (Named71.2, source) = (result, post)) :
    result = some (.result (.loc returnLabel returnOffset)) ∧
    post.regs.lookup 10 = some (.word pointer) ∧
    post.regs.lookup 24 = some (.word stack) ∧
    post.memory (globals + 18446744073709551584#64) =
      .word ((amount + pointer + 7#64) &&& 18446744073709551608#64) ∧
    post.mdomain = source.mdomain ∧ post.ffi = source.ffi ∧
    post.clock = source.clock - 4 ∧
    (∀ address, address ≠ globals + 18446744073709551584#64 →
      address ≠ stack - 32#64 + 24#64 → post.memory address = source.memory address) := by
  have roundedGuard : ¬ scratch < AndOp.and (amount + pointer + 7#64) (18446744073709551608#64) := roundedFits
  have mask : AndOp.and (18446744073709551608#64) (18446744073709551615#64) = 18446744073709551608#64 := by decide
  have zero : source.clock ≠ 0 := by omega
  have one : source.clock - 1 ≠ 0 := by omega
  have two : source.clock - 1 - 1 ≠ 0 := by omega
  have three : source.clock - 1 - 1 - 1 ≠ 0 := by omega
  simp [Named71, NamedBody71_0, NamedBody71_1, NamedBody71_2, NamedBody71_3, NamedBody71_4, NamedBody71_5, NamedBody71_6, NamedBody71_7, NamedBody71_8, NamedBody71_9, NamedBody71_10, NamedBody71_11, NamedBody71_12, NamedBody71_13, NamedBody71_14, NamedBody71_15, NamedBody71_16, NamedBody71_88, NamedBody71_89, NamedBody71_90, NamedBody71_91, NamedBody71_92, NamedBody71_93, NamedBody71_94, NamedBody71_95, NamedBody71_96, NamedBody71_97, NamedBody71_98, NamedBody71_99, NamedBody71_100, NamedBody71_101, NamedBody71_175, NamedBody71_176, NamedBody71_177, NamedBody71_178, NamedBody71_179, NamedBody71_180, NamedBody71_181, NamedBody71_182, NamedBody71_183, NamedBody71_184, NamedBody71_185, NamedBody71_186, NamedBody71_187, NamedBody71_188, NamedBody71_189, NamedBody71_190, NamedBody71_191, NamedBody71_192, NamedBody71_193, NamedBody71_194, NamedBody71_195, NamedBody71_196, NamedBody71_197, NamedBody71_198, NamedBody71_199, NamedBody71_200, NamedBody71_201, NamedBody71_202, NamedBody71_203, NamedBody71_204, NamedBody71_205, NamedBody71_206, NamedBody71_207, NamedBody71_208, NamedBody71_209, NamedBody71_210, NamedBody71_211, NamedBody71_212, NamedBody71_213, NamedBody71_214, NamedBody71_215, NamedBody71_216, NamedBody71_217, NamedBody71_218, NamedBody71_219, NamedBody71_220,
    seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
    StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
    wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger,
    assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
    hmetadata, hheap, hstack, hamount, hreturn, stackSafe,
    metadataDomain, metadataValue, globalsEq, pointerDomain, pointerValue,
    scratchDomain, scratchValue, saveDomain, metadataNotSave, scratchNotSave,
    fits, mask, roundedGuard, zero, one, two, three,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at execution
  rcases execution with ⟨rfl, rfl⟩
  simp [Nat.sub_sub, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  refine ⟨?_, rfl, ?_⟩
  · exact BitVec.sub_add_cancel stack 32#64
  · intro address notPointer notSave
    simp [notPointer, notSave]

end InitECandidate.Solver.GuestWork.FrameAllocEntry
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.updates
