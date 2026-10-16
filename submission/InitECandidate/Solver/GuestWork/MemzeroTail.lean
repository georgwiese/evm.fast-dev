import InitECandidate.Solver.FlattenWeighted.LoopClockRank
import InitECandidate.Proofs.BackendStages.Named78

namespace InitECandidate.Solver.GuestWork.MemzeroTail
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Actual final byte loop of fixed Named78 (memzero). -/
def body : HolProg 64 := NamedBody78_233

theorem body_basic : basic body = true := by decide
theorem body_nodes : nodes body = 27 := by decide
theorem body_ticks : ticks body = 2 := by decide

theorem body_work {C F : Type} (source : StackSemStateFiniteExact 64 C F) :
    Work body source 29 := by
  have h := Work.basic (source := source) body_basic
  simpa only [body_ticks, body_nodes] using h

theorem body_clock {C F : Type} (source : StackSemStateFiniteExact 64 C F) :
    source.clock ≤ (evaluate (body, source)).2.clock + 2 := by
  simpa only [body_ticks] using basicClock body source body_basic

private theorem evaluateSeq {C F : Type} (p q : HolProg 64)
    (s : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, s) =
      match evaluate (p, s) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, s) with ⟨result, next⟩
  cases result <;> rfl

/-- Any continuing body run preserves the length/base and increments the index.
A failed store or timeout cannot satisfy the actual continuation premise. -/
theorem body_continues {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (base length index : BitVec 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index))
    (execution : evaluate (body, source) = (result, post))
    (continues : StackSemControl.contLoop result = true) :
    post.regs.lookup 10 = some (.word base) ∧
      post.regs.lookup 11 = some (.word length) ∧
      post.regs.lookup 12 = some (.word (index + 1)) ∧ index < length := by
  by_cases less : index < length <;> by_cases zero : source.clock = 0
  all_goals cases store : memStoreByteAuxExact source.memory source.mdomain source.be (index + base) 0#8
  all_goals
    simp [body, NamedBody78_207, NamedBody78_208, NamedBody78_209, NamedBody78_210, NamedBody78_211, NamedBody78_212, NamedBody78_213, NamedBody78_214, NamedBody78_215, NamedBody78_216, NamedBody78_217, NamedBody78_218, NamedBody78_219, NamedBody78_220, NamedBody78_221, NamedBody78_222, NamedBody78_223, NamedBody78_224, NamedBody78_225, NamedBody78_226, NamedBody78_227, NamedBody78_228, NamedBody78_229, NamedBody78_230, NamedBody78_231, NamedBody78_232, NamedBody78_233,
      evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
      evaluate_inst, evaluate_continue, evaluate_break,
      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
      hbase, hlength, hindex, less, zero, store, wordSemWordCmp, wordCmpHOL,
      StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
      setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at execution
    rcases execution with ⟨rfl, rfl⟩
    simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end InitECandidate.Solver.GuestWork.MemzeroTail
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.body_basic
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.body_nodes
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.body_ticks
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.body_work
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.body_clock
#print axioms InitECandidate.Solver.GuestWork.MemzeroTail.body_continues
