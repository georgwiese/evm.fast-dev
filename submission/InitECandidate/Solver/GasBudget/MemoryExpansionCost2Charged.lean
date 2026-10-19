import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Range
import InitECandidate.Solver.GasBudget.ChargeWithMemoryExpansion
import InitECandidate.Solver.GasBudget.MemoryExtendGlobals

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

def chargedProgram (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "charge_gas") arguments)
    (.seq (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (localVar "x")]) continuation)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
/-- Reached normal charge and expansion for the actual two-range result.
Affordability, allocator funding and the final physical buffer are derived
from these real calls, while their actual continuation is retained. -/
theorem charged_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch amount : BitVec 64) (s1 n1 s2 n2 : U256Value.Words)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (xLocal : source.locals.lookup (ofString "x") = some (MemoryExpansionCost.pairValue (resultPair s1 n1 s2 n2 current)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (covers : (resultPair s1 n1 s2 n2 current).1.toNat ≤ amount.toNat)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word amount)])
    (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (chargedProgram arguments continuation) = (some (.returned returned), post)) :
    ∃ ready : PanSemStateFiniteExact 64 Guest.HostMemory,
      MemoryExtend.price current capacity (resultPair s1 n1 s2 n2 current).2 + 2 ≤ source.clock ∧
      ready.clock = source.clock - (MemoryExtend.price current capacity (resultPair s1 n1 s2 n2 current).2 + 2) ∧
      ready.locals = source.locals ∧
      MemoryExtend.View ready frame base (MemoryExtend.newLength current (resultPair s1 n1 s2 n2 current).2)
        (MemoryExtend.nextCapacity current capacity (resultPair s1 n1 s2 n2 current).2)
        (base + MemoryExtend.nextCapacity current capacity (resultPair s1 n1 s2 n2 current).2) scratch ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + amount.toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (resultPair s1 n1 s2 n2 current).2)).toNat ≤
        (wordAt ready.memory (frame + 184#64)).toNat ∧
      ChargeWithMemory.OutsideEffect source ready frame base scratch ∧
      (U256Zero.resultWord n1 = 0#64 → (SatWord.resultWord s1).toNat + (SatWord.resultWord n1).toNat ≤
        (MemoryExtend.newLength current (resultPair s1 n1 s2 n2 current).2).toNat) ∧
      (U256Zero.resultWord n2 = 0#64 → (SatWord.resultWord s2).toNat + (SatWord.resultWord n2).toNat ≤
        (MemoryExtend.newLength current (resultPair s1 n1 s2 n2 current).2).toNat) ∧
      (∀ key, key ≠ ofString "frame_mem_ptr" → ready.globals.lookup key = source.globals.lookup key) ∧
      ready.memaddrs = source.memaddrs ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), post) := by
  let expand := (resultPair s1 n1 s2 n2 current).2
  have chargeSafe : Input.LocalPrefix (ofString "x") (.call (some (none, none)) (ofString "charge_gas") arguments) := .call none _ _ (by simp)
  obtain ⟨charged, chargeRun, suffixRun, xRetained⟩ := chargeSafe.normal_continue source post _ returned normal
  obtain ⟨gas, used, chargeFits, chargeClock, gasMapped, usedMapped, gasCell, usedCell, affordable, chargeFrame, chargeBudget, debit, credit⟩ :=
    RegularCharge.call_normal source charged frame amount arguments args
      (OriginalCodeEnvironment.charge_gas source.code view.installed) view.ev cap chargeRun
  have chargedView := view.after_charge source charged frame base current capacity pointer scratch amount arguments args cap chargeRun
  have oldUsed : (wordAt source.memory (frame + 184#64)).toNat = used.toNat := by simp [wordAt, usedCell, MemoryBytes.wordBits]
  have pool : used.toNat + gas.toNat ≤ 16777216 := by
    simp only [regularBudget, wordAt, gasCell, usedCell, MemoryBytes.wordBits] at cap
    omega
  have advance := MemoryExpansionCost2.affordable s1 n1 s2 n2 current amount used.toNat gas.toNat view.lengthAligned
    (by rw [oldUsed] at covered; exact covered) pool (BitVec.le_def.mp affordable) covers
  have finite : (resultPair s1 n1 s2 n2 current).1 ≠ 18446744073709551615#64 := by
    intro equal
    have number := congrArg BitVec.toNat equal
    change (resultPair s1 n1 s2 n2 current).1.toNat = 18446744073709551615 at number
    have available := BitVec.le_def.mp affordable
    omega
  obtain ⟨firstRange, secondRange⟩ := ranges s1 n1 s2 n2 current view.lengthAligned finite
  have extendSafe : Input.LocalPrefix (ofString "x") (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (localVar "x")]) := .call none _ _ (by simp)
  obtain ⟨ready, extendRun, tailRun, saved⟩ := extendSafe.normal_continue charged post continuation returned suffixRun
  have extendArgs : evalListHOLFinite charged (h := fun address => Classical.propDecidable (charged.memaddrs address)) [.rfield 1 (localVar "x")] = some [.val (.word expand)] := by
    have cell := xRetained.trans xLocal
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, cell, MemoryExpansionCost.pairValue, expand]
  obtain ⟨extendFits, extendClock, readyView, budgetSum, usedSum⟩ :=
    MemoryExtend.call_sums charged ready frame base current capacity pointer scratch expand amount used.toNat [.rfield 1 (localVar "x")]
      chargedView advance extendArgs [] (by simp) (by simp) extendRun
  obtain ⟨_, _, _, locals, extendAway⟩ := MemoryExtend.call_normal charged ready frame base current capacity pointer scratch expand amount used.toNat
    [.rfield 1 (localVar "x")] chargedView advance extendArgs extendRun
  have readyBudget : regularBudget ready.memory frame = regularBudget charged.memory frame := by simpa [FrameSums.budget] using budgetSum
  have readyUsed : (wordAt ready.memory (frame + 184#64)).toNat = (wordAt charged.memory (frame + 184#64)).toNat := by simpa [FrameSums.used] using usedSum
  refine ⟨ready, ?_, ?_, ?_, readyView, readyBudget.trans chargeBudget, ?_, ?_, ?_, firstRange, secondRange, ?_, ?_, tailRun⟩
  · rw [chargeClock] at extendFits
    change MemoryExtend.price current capacity expand + 2 ≤ source.clock
    omega
  · rw [extendClock, chargeClock]
    change source.clock - 1 - (MemoryExtend.price current capacity expand + 1) = source.clock - (MemoryExtend.price current capacity expand + 2)
    omega
  · rw [locals, chargeFrame]
  · rw [readyUsed, credit, oldUsed]
  · change (MemoryGasCost.resultWord (current + expand)).toNat ≤ _
    rw [readyUsed, credit]
    exact advance.covered
  · intro query outside notLength notCapacity notGas notUsed
    rw [extendAway query outside notLength notCapacity]
    exact RegularCharge.call_other_word source charged frame amount query arguments args
      (OriginalCodeEnvironment.charge_gas source.code view.installed) view.ev cap chargeRun notGas notUsed
  · intro key different
    have global := MemoryExtend.call_global_other charged ready frame base current capacity pointer scratch expand amount used.toNat
      [.rfield 1 (localVar "x")] chargedView advance extendArgs extendRun key different
    rw [global, chargeFrame]
  · have extendFields := Input.evaluation_fields charged ready _ none extendRun
    have chargeFields := Input.evaluation_fields source charged _ none chargeRun
    exact extendFields.1.trans chargeFields.1

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.charged_normal
