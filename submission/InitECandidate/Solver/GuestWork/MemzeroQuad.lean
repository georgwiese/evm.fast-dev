import InitECandidate.Solver.FlattenWeighted.LoopClockRank
import InitECandidate.Proofs.BackendStages.Named78

namespace InitECandidate.Solver.GuestWork.MemzeroQuad
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Actual aligned thirty-two-byte loop of fixed Named78 (memzero). -/
def body : HolProg 64 := NamedBody78_67

theorem body_basic : basic body = true := by decide
theorem body_nodes : nodes body = 59 := by decide
theorem body_ticks : ticks body = 2 := by decide

theorem body_work {C F : Type} (source : StackSemStateFiniteExact 64 C F) :
    Work body source 61 := by
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
      post.regs.lookup 12 = some (.word (index + 32#64)) ∧ index + 32#64 ≤ length) ∧
    (result = some (.break 0) →
      post.regs.lookup 10 = some (.word base) ∧
      post.regs.lookup 11 = some (.word length) ∧
      post.regs.lookup 12 = some (.word index) ∧ length < index + 32#64) := by
  by_cases less : length < index + 32#64 <;> by_cases zero : source.clock = 0
  all_goals by_cases domain : source.mdomain (index + base) = true
  all_goals by_cases domain8 : source.mdomain (index + base + 8#64) = true
  all_goals by_cases domain16 : source.mdomain (index + base + 16#64) = true
  all_goals by_cases domain24 : source.mdomain (index + base + 24#64) = true
  all_goals
    simp [body, NamedBody78_9, NamedBody78_10, NamedBody78_11, NamedBody78_12, NamedBody78_13, NamedBody78_14, NamedBody78_15, NamedBody78_16, NamedBody78_17, NamedBody78_18, NamedBody78_19, NamedBody78_20, NamedBody78_21, NamedBody78_22, NamedBody78_23, NamedBody78_24, NamedBody78_25, NamedBody78_26, NamedBody78_27, NamedBody78_28, NamedBody78_29, NamedBody78_30, NamedBody78_31, NamedBody78_32, NamedBody78_33, NamedBody78_34, NamedBody78_35, NamedBody78_36, NamedBody78_37, NamedBody78_38, NamedBody78_39, NamedBody78_40, NamedBody78_41, NamedBody78_42, NamedBody78_43, NamedBody78_44, NamedBody78_45, NamedBody78_46, NamedBody78_47, NamedBody78_48, NamedBody78_49, NamedBody78_50, NamedBody78_51, NamedBody78_52, NamedBody78_53, NamedBody78_54, NamedBody78_55, NamedBody78_56, NamedBody78_57, NamedBody78_58, NamedBody78_59, NamedBody78_60, NamedBody78_61, NamedBody78_62, NamedBody78_63, NamedBody78_64, NamedBody78_65, NamedBody78_66, NamedBody78_67,
      evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
      evaluate_inst, evaluate_continue, evaluate_break,
      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
      hbase, hlength, hindex, less, zero, domain, domain8, domain16, domain24, wordSemWordCmp, wordCmpHOL,
      StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
      StackSemStateOps.memStore, setVar, decClock, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL] at execution
    rcases execution with ⟨rfl, rfl⟩
    simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

end InitECandidate.Solver.GuestWork.MemzeroQuad
#print axioms InitECandidate.Solver.GuestWork.MemzeroQuad.body_basic
#print axioms InitECandidate.Solver.GuestWork.MemzeroQuad.body_nodes
#print axioms InitECandidate.Solver.GuestWork.MemzeroQuad.body_ticks
#print axioms InitECandidate.Solver.GuestWork.MemzeroQuad.body_work
#print axioms InitECandidate.Solver.GuestWork.MemzeroQuad.body_clock
#print axioms InitECandidate.Solver.GuestWork.MemzeroQuad.body_outcome
