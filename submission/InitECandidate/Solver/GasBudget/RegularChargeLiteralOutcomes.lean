import InitECandidate.Solver.GasBudget.RegularChargeOutcomes
import InitECandidate.Solver.GasBudget.RegularChargeMemory

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def literalResult (clock : Nat) (gas amount : BitVec 64) : Option (PanSemResultExact 64) :=
  if clock = 0 then some .timeOut
  else if amount ≤ gas then none else some (.exception (ofString "EvmErr") (.val (.word 4#64)))

def literalDebit (clock : Nat) (gas amount : BitVec 64) : Nat :=
  if clock = 0 then 0 else debit gas amount

/-- Total actual literal charge call, including clock-zero timeout. The real
code lookup supplies its callee; its argument evaluation and all caller/body
clocks are derived. Only affordable funded calls credit the used counter. -/
theorem literal_outcomes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used amount : BitVec 64)
    (code : source.code.lookup (ofString "charge_gas") = some (formals, body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one) :
    ∃ target, evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_gas") [.const amount]) =
        (literalResult source.clock gas amount, target) ∧
      target.clock = source.clock - 1 ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := source.clock - 1} ∧
      target.memory = (if source.clock = 0 then source.memory else memoryAfter source.memory frame gas used amount) ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = used.toNat + literalDebit source.clock gas amount ∧
      ∀ address, address ≠ frame + 64#64 → address ≠ frame + 184#64 → target.memory address = source.memory address := by
  classical
  by_cases zero : source.clock = 0
  · obtain ⟨callee, called, amountLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "charge_gas") "amount" body amount code
    have sameClock : source.clock - 1 = source.clock := by omega
    refine ⟨emptyLocalsHOLFinite source, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · rw [evaluateHOLFiniteState_call]
      simp only [evalListHOLFinite, evalListHOLExact, evalHOLExact, called, if_pos zero, literalResult]
    · exact sameClock.symm
    · rw [sameClock]
      rfl
    · simp only [if_pos zero]
      rfl
    · change (wordAt source.memory (frame + 184#64)).toNat = used.toNat + literalDebit source.clock gas amount
      simp only [wordAt, usedCell, MemoryBytes.wordBits, literalDebit, if_pos zero, Nat.add_zero]
    · intro address _ _
      rfl
  · have enough : 1 ≤ source.clock := by omega
    by_cases affordable : amount ≤ gas
    · obtain ⟨memory, run, budget, debit, credit⟩ := call_execute source frame gas used amount [.const amount] rfl code ev gasMapped usedMapped gasCell usedCell
        affordable (ledger_fits source frame gas used gasCell usedCell cap) enough
      refine ⟨{source with memory := memory, clock := source.clock - 1}, ?_, rfl, rfl, ?_, budget, ?_, ?_⟩
      · simpa only [literalResult, if_neg zero, if_pos affordable] using run
      · obtain ⟨actualGas, actualUsed, actualGasCell, actualUsedCell, memoryEq⟩ := call_memory source _ frame amount [.const amount] rfl code ev cap run
        have gasEq : actualGas = gas := HolWordLab.word.inj (actualGasCell.symm.trans gasCell)
        have usedEq : actualUsed = used := HolWordLab.word.inj (actualUsedCell.symm.trans usedCell)
        simpa only [if_neg zero, memoryAfter, if_pos affordable, gasEq, usedEq] using memoryEq
      · simpa only [literalDebit, if_neg zero, RegularCharge.debit, if_pos affordable] using credit
      · intro address notGas notUsed
        exact call_other_word source _ frame amount address [.const amount] rfl code ev cap run notGas notUsed
    · have unavailable : gas < amount := by change ¬amount.toNat ≤ gas.toNat at affordable; change gas.toNat < amount.toNat; omega
      have run := failed_call source frame gas amount [.const amount] rfl code ev gasMapped gasCell unavailable exceptionShape enough
      refine ⟨emptyLocalsHOLFinite {source with clock := source.clock - 1}, ?_, rfl, rfl, ?_, rfl, ?_, ?_⟩
      · simpa only [literalResult, if_neg zero, if_neg affordable] using run
      · simp only [if_neg zero, memoryAfter, if_neg affordable]
        rfl
      · change (wordAt source.memory (frame + 184#64)).toNat = used.toNat + literalDebit source.clock gas amount
        simp only [wordAt, usedCell, MemoryBytes.wordBits, literalDebit, if_neg zero, RegularCharge.debit, if_neg affordable, Nat.add_zero]
      · intro address _ _
        rfl

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.literal_outcomes
