import InitECandidate.Solver.GasBudget.StackPopsPrefix
import InitECandidate.Solver.GasBudget.RegularChargeMemory

namespace InitECandidate.Solver.GasBudget.OpcodeChargePrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def program (names : List String) (amount : BitVec 64) (continuation : ProgHOL 64) : ProgHOL 64 :=
  StackPop.pops names (.seq (.call (some (none, none)) (ofString "charge_gas") [.const amount]) continuation)

/-- Real pop-prefix and charge execution before a real opcode suffix.
This proves charge progress at suffix entry; suffix preservation and the
opcode's final outcome must still be proved separately. -/
theorem normal (names : List String) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame amount : BitVec 64)
    (continuation : ProgHOL 64)
    (stackCode : source.code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (program names amount continuation) = (some (.returned value), post)) :
    ∃ ready inner, names.length + 1 ≤ source.clock ∧ ready.clock = source.clock - (names.length + 1) ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - (names.length + 1)} ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + amount.toNat ∧
      (wordAt ready.memory (frame + 16#64)).toNat + names.length = (wordAt source.memory (frame + 16#64)).toNat ∧
      (∀ address, address ≠ frame + 16#64 → address ≠ frame + 64#64 → address ≠ frame + 184#64 →
        ready.memory address = source.memory address) := by
  obtain ⟨popped, scopePost, popFits, popClock, popFrame, poppedRun, scopeEq, popBudget, popUsed, popOutside, popDepth⟩ :=
    StackPop.pops_normal names source post frame _ stackCode ev value run
  have poppedGlobals := congrArg PanSemStateFiniteExact.globals popFrame
  change popped.globals = source.globals at poppedGlobals
  have poppedCode := congrArg PanSemStateFiniteExact.code popFrame
  change popped.code = source.code at poppedCode
  have poppedEV : popped.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [poppedGlobals]; exact ev
  have poppedCharge : popped.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one) := by rw [poppedCode]; exact chargeCode
  have poppedCap : regularBudget popped.memory frame ≤ 16777216 := by rw [popBudget]; exact cap
  have safe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "charge_gas") [.const amount]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨charged, chargeRun, continuationRun, saved⟩ := safe.normal_continue popped scopePost continuation value poppedRun
  obtain ⟨gas, used, chargeFits, chargeClock, gasMapped, usedMapped, gasCell, usedCell, affordable, chargeFrame, chargeBudget, debit, credit⟩ :=
    RegularCharge.call_normal popped charged frame amount [.const amount] rfl poppedCharge poppedEV poppedCap chargeRun
  have sub : source.clock - names.length - 1 = source.clock - (names.length + 1) := by omega
  have chargedFrame : emptyLocalsHOLFinite charged = emptyLocalsHOLFinite {source with memory := charged.memory, clock := source.clock - (names.length + 1)} := by
    have first := congrArg emptyLocalsHOLFinite chargeFrame
    have second := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
      {state with memory := charged.memory, clock := popped.clock - 1}) popFrame
    have combined := first.trans second
    rw [popClock, sub] at combined
    exact combined
  refine ⟨charged, scopePost, by omega, by rw [chargeClock, popClock, sub], chargedFrame, continuationRun, scopeEq,
    chargeBudget.trans popBudget, ?_, ?_, ?_⟩
  · have oldUsed : wordAt source.memory (frame + 184#64) = used := by
      unfold wordAt
      rw [← popUsed, usedCell]
      rfl
    rw [credit, oldUsed]
  · have spSame := RegularCharge.call_other_word popped charged frame amount (frame + 16#64) [.const amount] rfl poppedCharge poppedEV poppedCap chargeRun
      (offsets_ne frame 16#64 64#64 (by decide)) (offsets_ne frame 16#64 184#64 (by decide))
    change (WitnessRadix.MemoryBytes.wordBits (charged.memory (frame + 16#64))).toNat + names.length = _
    rw [spSame]
    exact popDepth
  · intro address notSP notGas notUsed
    exact (RegularCharge.call_other_word popped charged frame amount address [.const amount] rfl poppedCharge poppedEV poppedCap chargeRun notGas notUsed).trans
      (popOutside address notSP)

end InitECandidate.Solver.GasBudget.OpcodeChargePrefix

#print axioms InitECandidate.Solver.GasBudget.OpcodeChargePrefix.normal
