import InitECandidate.Solver.FlattenWeighted.LoopClockRank
import InitECandidate.Proofs.BackendStages.Named78

namespace InitECandidate.Solver.GuestWork.MemzeroWord
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Actual aligned eight-byte loop of fixed Named78 (memzero). -/
def body : HolProg 64 := NamedBody78_100

theorem body_basic : basic body = true := by decide
theorem body_nodes : nodes body = 29 := by decide
theorem body_ticks : ticks body = 2 := by decide

theorem body_work {C F : Type} (source : StackSemStateFiniteExact 64 C F) :
    Work body source 31 := by
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

/-- Successful continuation and normal loop exit expose the actual guard and
register updates. Failed stores and timeouts satisfy neither premise. -/
theorem body_outcome {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (base length index : BitVec 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (hindex : source.regs.lookup 12 = some (.word index))
    (execution : evaluate (body, source) = (result, post)) :
    (StackSemControl.contLoop result = true →
      post.regs.lookup 10 = some (.word base) ∧
      post.regs.lookup 11 = some (.word length) ∧
      post.regs.lookup 12 = some (.word (index + 8#64)) ∧ index + 8#64 ≤ length) ∧
    (result = some (.break 0) →
      post.regs.lookup 10 = some (.word base) ∧
      post.regs.lookup 11 = some (.word length) ∧
      post.regs.lookup 12 = some (.word index) ∧ length < index + 8#64) := by
  by_cases less : length < index + 8#64 <;> by_cases zero : source.clock = 0
  all_goals by_cases domain : source.mdomain (index + base) = true
  all_goals
    simp [body, NamedBody78_72, NamedBody78_73, NamedBody78_74, NamedBody78_75, NamedBody78_76, NamedBody78_77, NamedBody78_78, NamedBody78_79, NamedBody78_80, NamedBody78_81, NamedBody78_82, NamedBody78_83, NamedBody78_84, NamedBody78_85, NamedBody78_86, NamedBody78_87, NamedBody78_88, NamedBody78_89, NamedBody78_90, NamedBody78_91, NamedBody78_92, NamedBody78_93, NamedBody78_94, NamedBody78_95, NamedBody78_96, NamedBody78_97, NamedBody78_98, NamedBody78_99, NamedBody78_100,
      evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
      evaluate_inst, evaluate_continue, evaluate_break,
      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
      hbase, hlength, hindex, less, zero, domain, wordSemWordCmp, wordCmpHOL,
      StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
      StackSemStateOps.memStore, setVar, decClock, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL] at execution
    rcases execution with ⟨rfl, rfl⟩
    simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end InitECandidate.Solver.GuestWork.MemzeroWord
#print axioms InitECandidate.Solver.GuestWork.MemzeroWord.body_basic
#print axioms InitECandidate.Solver.GuestWork.MemzeroWord.body_nodes
#print axioms InitECandidate.Solver.GuestWork.MemzeroWord.body_ticks
#print axioms InitECandidate.Solver.GuestWork.MemzeroWord.body_work
#print axioms InitECandidate.Solver.GuestWork.MemzeroWord.body_clock
#print axioms InitECandidate.Solver.GuestWork.MemzeroWord.body_outcome
