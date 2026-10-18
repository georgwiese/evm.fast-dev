import InitECandidate.Solver.GasBudget.RegularChargeNormal
import InitECandidate.Solver.Input.QuietClock

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

theorem body_clock (code) : Input.QuietClock.Preserves code body := by
  rw [body_shape]
  apply Input.QuietClock.declared
  apply Input.QuietClock.sequence
  · apply Input.QuietClock.conditional
    · exact Input.QuietClock.raised code _ _
    · exact Input.QuietClock.skip code
  · unfold afterGuard
    apply Input.QuietClock.sequence
    · exact Input.QuietClock.store code _ _
    · apply Input.QuietClock.sequence
      · exact Input.QuietClock.store code _ _
      · exact Input.QuietClock.returned code _

def outcome (gas amount : BitVec 64) : PanSemResultExact 64 :=
  if amount ≤ gas then .returned (.val (.word 0#64))
  else .exception (ofString "EvmErr") (.val (.word 4#64))

def memoryAfter (memory : Memory) (frame gas used amount : BitVec 64) : Memory :=
  if amount ≤ gas then WordWrites.write memory (writes frame gas used amount) else memory

def debit (gas amount : BitVec 64) : Nat := if amount ≤ gas then amount.toNat else 0

/-- Total execution of the original charge body on actual mapped gas words.
An affordable charge credits used gas; an insufficient charge really throws
before mutation. No normal execution or future clock funding is assumed. -/
theorem body_outcomes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used amount : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (amountLocal : source.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one) :
    ∃ target, evaluateHOLFiniteState source body = (some (outcome gas amount), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memoryAfter source.memory frame gas used amount} ∧
      target.clock = source.clock ∧ regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = used.toNat + debit gas amount ∧
      (wordAt target.memory (frame + 64#64)).toNat + debit gas amount = gas.toNat ∧
      ∀ address, address ≠ frame + 64#64 → address ≠ frame + 184#64 → target.memory address = source.memory address := by
  by_cases affordable : amount ≤ gas
  · obtain ⟨target, run, memory, frameEq⟩ := execute source frame gas used amount ev amountLocal gasMapped usedMapped gasCell usedCell affordable
    have quantitative := quantitative source frame gas used amount gasCell usedCell affordable (ledger_fits source frame gas used gasCell usedCell cap)
    have clock := body_clock source.code source rfl
    rw [run] at clock
    refine ⟨target, ?_, ?_, clock, ?_, ?_, ?_, ?_⟩
    · simpa only [outcome, if_pos affordable] using run
    · rw [frameEq, memoryAfter, if_pos affordable, memory]
    · rw [memory]
      exact quantitative.1
    · rw [memory, debit, if_pos affordable]
      exact quantitative.2.2
    · rw [memory, debit, if_pos affordable]
      exact quantitative.2.1
    · intro address awayGas awayUsed
      rw [memory]
      exact WordWrites.write_away source.memory (writes frame gas used amount) address (by simp [writes, awayGas, awayUsed])
  · have unavailable : gas < amount := by change ¬amount.toNat ≤ gas.toNat at affordable; change gas.toNat < amount.toNat; omega
    obtain ⟨target, run, frameEq⟩ := failed source frame gas amount ev amountLocal gasMapped gasCell unavailable exceptionShape
    have memory := congrArg PanSemStateFiniteExact.memory frameEq
    change target.memory = source.memory at memory
    have clock := body_clock source.code source rfl
    rw [run] at clock
    refine ⟨target, ?_, ?_, clock, ?_, ?_, ?_, ?_⟩
    · simpa only [outcome, if_neg affordable] using run
    · simpa only [memoryAfter, if_neg affordable] using frameEq
    · rw [memory]
    · simp only [memory, wordAt, usedCell, MemoryBytes.wordBits, debit, if_neg affordable, Nat.add_zero]
    · simp only [memory, wordAt, gasCell, MemoryBytes.wordBits, debit, if_neg affordable, Nat.add_zero]
    · intro address _ _
      exact congrFun memory address

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.body_clock
#print axioms InitECandidate.Solver.GasBudget.RegularCharge.body_outcomes
