import InitECandidate.Solver.GuestWork.MemzeroFrame
import InitECandidate.Solver.GuestWork.MemzeroMemory
import InitECandidate.Solver.GuestWork.MemzeroCall
import InitECandidate.Proofs.BackendStages.Named484

namespace InitECandidate.Solver.GuestWork.ExtendMemoryRestore
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

/-- Actual return continuation of the capacity-clearing call restores a bounded
logical extension length. Only separation from the handler-metadata store is
required; failed loads/stores cannot satisfy normal completion. -/
theorem capacity_restore {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (stack metadata : BitVec 64) (maximum : Nat)
    (hstack : source.regs.lookup 24 = some (.word stack))
    (hmetadata : source.regs.lookup 25 = some (.word metadata))
    (bounded : ∃ value, source.memory (stack + 24#64 + 32#64) = .word value ∧ value.toNat ≤ maximum)
    (separated : stack + 24#64 + 32#64 ≠ metadata + 18446744073709551560#64)
    (execution : evaluate (NamedBody484_202, source) = (none, post)) :
    (∃ value, post.regs.lookup 11 = some (.word value) ∧ value.toNat ≤ maximum) ∧
    post.code = source.code ∧
    post.regs.lookup 24 = some (.word (stack + 24#64)) ∧
    post.regs.lookup 25 = some (.word metadata) := by
  obtain ⟨value, found, small⟩ := bounded
  by_cases domain0 : source.mdomain (stack + 16#64) = true <;>
    by_cases domain1 : source.mdomain (metadata + 18446744073709551560#64) = true <;>
    by_cases domain2 : source.mdomain (stack + 24#64 + 40#64) = true <;>
    by_cases domain3 : source.mdomain (stack + 24#64 + 32#64) = true <;>
    by_cases domain4 : source.mdomain (stack + 24#64 + 24#64) = true <;>
    by_cases domain5 : source.mdomain (stack + 24#64 + 16#64) = true
  all_goals
    simp [NamedBody484_186, NamedBody484_187, NamedBody484_188, NamedBody484_189, NamedBody484_190, NamedBody484_191, NamedBody484_192, NamedBody484_193, NamedBody484_194, NamedBody484_195, NamedBody484_196, NamedBody484_197, NamedBody484_198, NamedBody484_199, NamedBody484_200, NamedBody484_201, NamedBody484_202,
      seqEvaluate, evaluate_skip, evaluate_inst, StackSemInst.instHOL, instInteger,
      assign, wordExp, wordOpHOL, wordOp, memLoad, memStore, getVar, setVar,
      hstack, hmetadata, found, separated,
      domain0, domain1, domain2, domain3, domain4, domain5,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at execution
  all_goals
    subst post
    exact ⟨⟨value, by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL], small⟩, rfl,
      by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL],
      by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hmetadata]⟩


/-- Transfer the saved expansion-length bound through the actual first
memzero call and its compiled return continuation. Zeroing may overlap the
saved slot; only the distinct handler-metadata store requires separation. -/
theorem capacity_call_saved_length {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (stack metadata : BitVec 64) (maximum : Nat)
    (installed : sptLookup 78 source.code = some Named78.2)
    (hstack : source.regs.lookup 24 = some (.word stack))
    (hmetadata : source.regs.lookup 25 = some (.word metadata))
    (bounded : ∃ value, source.memory (stack + 24#64 + 32#64) = .word value ∧ value.toNat ≤ maximum)
    (separated : stack + 24#64 + 32#64 ≠ metadata + 18446744073709551560#64)
    (execution : evaluate (NamedBody484_214, source) = (none, post)) :
    (∃ value, post.regs.lookup 11 = some (.word value) ∧ value.toNat ≤ maximum) ∧
    post.code = source.code ∧
    post.regs.lookup 24 = some (.word (stack + 24#64)) ∧
    post.regs.lookup 25 = some (.word metadata) := by
  rw [NamedBody484_214, evaluate_call] at execution
  simp only [StackSemControl.findCode, installed] at execution
  by_cases zero : source.clock = 0
  · simp [zero] at execution
  simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
  rcases run : evaluate (Named78.2, decClock (setVar 1 (.loc 484 4) source)) with ⟨result, middle⟩
  rw [run] at execution
  have noException := MemzeroCall.no_exception (decClock (setVar 1 (.loc 484 4) source))
  rw [run] at noException
  cases result with
  | none => simp at execution
  | some outcome =>
    cases outcome with
    | result value =>
      by_cases same : value = .loc 484 4
      · subst value
        simp only [ne_eq, not_true_eq_false, if_false] at execution
        have stackFrame := MemzeroFrame.entered_register source middle _ 484 4 24 (by simp) run (by simp)
        have metadataFrame := MemzeroFrame.entered_register source middle _ 484 4 25 (by simp) run (by simp)
        have saved := MemzeroMemory.saved_length (decClock (setVar 1 (.loc 484 4) source))
          middle _ (stack + 24#64 + 32#64) maximum bounded run
        have restored := capacity_restore middle post stack metadata maximum
          (stackFrame.1.trans hstack) (metadataFrame.1.trans hmetadata) saved separated execution
        exact ⟨restored.1, restored.2.1.trans stackFrame.2, restored.2.2⟩
      · simp [same] at execution
    | exception value => exact (noException value rfl).elim
    | _ => simp at execution

end InitECandidate.Solver.GuestWork.ExtendMemoryRestore
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryRestore.capacity_restore

#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryRestore.capacity_call_saved_length
