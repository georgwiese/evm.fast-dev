import InitECandidate.Solver.GuestWork.ExtendMemoryLength
import InitECandidate.Solver.FlattenWeighted.BlockPrefix

namespace InitECandidate.Solver.GuestWork.ExtendMemoryZero
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def ready {C F : Type} (source : StackSemStateFiniteExact 64 C F) : Prop :=
  source.regs.lookup 10 = some (.word 0#64) ∧ ∃ stack metadata,
    source.regs.lookup 24 = some (.word stack) ∧ source.regs.lookup 25 = some (.word metadata)

def entryBlocks : List (HolProg 64) := [NamedBody484_6, NamedBody484_7, NamedBody484_8, NamedBody484_19]

private theorem seqEvaluate {C F : Type} (p q : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

/-- Zero expansion exits before all frame reads, allocation and memzero calls.
This includes stack-overflow halts and malformed return locations. -/
theorem exits {C F : Type} (source post : StackSemStateFiniteExact 64 C F)
    (valid : ready source) (run : evaluate (prefixChain entryBlocks .skip, source) = (none, post)) : False := by
  obtain ⟨hamount, stack, metadata, hstack, hmetadata⟩ := valid
  by_cases lower : stack - 56#64 < metadata <;> by_cases zero : source.clock = 0
  all_goals
    simp [entryBlocks, prefixChain, NamedBody484_0, NamedBody484_1, NamedBody484_2, NamedBody484_3, NamedBody484_4, NamedBody484_5, NamedBody484_6, NamedBody484_7, NamedBody484_8, NamedBody484_9, NamedBody484_10, NamedBody484_11, NamedBody484_12, NamedBody484_13, NamedBody484_14, NamedBody484_15, NamedBody484_16, NamedBody484_17, NamedBody484_18, NamedBody484_19,
      seqEvaluate, evaluate_skip, evaluate_inst, evaluate_tick, evaluate_ite,
      evaluate_ret, evaluate_halt, StackSemInst.instHOL, instInteger, assign,
      wordExp, wordOpHOL, wordOp, wordShiftHOL,
      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
      wordSemWordCmp, wordCmpHOL, setVar, decClock, hamount, hstack, hmetadata, lower, zero,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at run
  all_goals
    repeat' split at *
    all_goals simp_all

/-- Bound for the complete fixed extend_memory routine at zero expansion. -/
theorem entry_bound {C F : Type} :
    BlockBound (C := C) (F := F) Named484.2 ready (fun _ => True) 21 1 := by
  have tail : BlockBound (C := C) (F := F) NamedBody484_376 (fun _ => False) (fun _ => True) 0 0 := {
    work := fun _ h => h.elim
    clock := fun _ h => h.elim
    normal := fun _ _ h _ => h.elim
    timeout := fun _ _ h _ => h.elim }
  have combined := BlockBound.basicPrefix entryBlocks NamedBody484_376 ready (fun _ => False)
    (fun _ => True) 0 0
    (by intro prog member; simp only [entryBlocks, List.mem_cons, List.mem_nil_iff, or_false] at member
        rcases member with h | h | h | h <;> subst prog <;> decide)
    exits tail
  apply combined.weaken (fun _ h => h) (fun _ h => h) <;>
    simp [prefixCredits, prefixClocks, entryBlocks, ticks, nodes, NamedBody484_0, NamedBody484_1, NamedBody484_2, NamedBody484_3, NamedBody484_4, NamedBody484_5, NamedBody484_6, NamedBody484_7, NamedBody484_8, NamedBody484_9, NamedBody484_10, NamedBody484_11, NamedBody484_12, NamedBody484_13, NamedBody484_14, NamedBody484_15, NamedBody484_16, NamedBody484_17, NamedBody484_18, NamedBody484_19]

theorem bounded_entry {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (valid : ready source) (run : evaluate (Named484.2, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (Named484.2, {source with clock := 2}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work Named484.2 {source with clock := 2} 21 :=
  entry_bound.boundedExecution (fun _ _ h => h) source post result valid run notTimeout

end InitECandidate.Solver.GuestWork.ExtendMemoryZero
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryZero.exits
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryZero.entry_bound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryZero.bounded_entry
