import InitECandidate.Solver.GasBudget.ChargeWithMemoryValueSetup
import InitECandidate.Solver.GasBudget.MemoryExtendChargeView
import InitECandidate.Solver.GasBudget.MemoryExtendFrameSums

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

theorem suffix_shape : suffix = .seq (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (localVar "x")]) MemoryExtend.returnZero := by
  simp only [suffix, body, Guest.guestFn_charge_with_memory, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, MemoryExtend.returnZero, localVar]

def OutsideEffect (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch : BitVec 64) : Prop :=
  ∀ query, Arenas.Outside base scratch query → query ≠ frame + 32#64 → query ≠ frame + 40#64 →
    query ≠ frame + 64#64 → query ≠ frame + 184#64 → post.memory query = source.memory query

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem after_total_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch fee : BitVec 64) (start size : U256Value.Words)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (xLocal : source.locals.lookup (ofString "x") = some (MemoryExpansionCost.pairValue (MemoryExpansionCost.resultPair start size current)))
    (totalLocal : source.locals.lookup (ofString "total") = some (.val (.word (SaturatingAdd.resultWord fee (MemoryExpansionCost.resultPair start size current).1))))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterTotal = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧
      MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 2 ≤ source.clock ∧
      post.clock = source.clock - (MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 2) ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord fee (MemoryExpansionCost.resultPair start size current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧ OutsideEffect source post frame base scratch := by
  let amount := SaturatingAdd.resultWord fee (MemoryExpansionCost.resultPair start size current).1
  let expand := (MemoryExpansionCost.resultPair start size current).2
  have chargeSafe : Input.LocalPrefix (ofString "x") (.call (some (none, none)) (ofString "charge_gas") [localVar "total"]) := .call none _ _ (by simp)
  obtain ⟨charged, chargeRun, suffixRun, xRetained⟩ := chargeSafe.normal_continue source post suffix returned normal
  have chargeArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "total"] = some [.val (.word amount)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, totalLocal, amount]
  obtain ⟨gas, used, chargeFits, chargeClock, gasMapped, usedMapped, gasCell, usedCell, affordable, chargeFrame, chargeBudget, debit, credit⟩ :=
    RegularCharge.call_normal source charged frame amount [localVar "total"] chargeArgs
      (OriginalCodeEnvironment.charge_gas source.code view.installed) view.ev cap chargeRun
  have chargedView := view.after_charge source charged frame base current capacity pointer scratch amount [localVar "total"] chargeArgs cap chargeRun
  have oldUsed : (wordAt source.memory (frame + 184#64)).toNat = used.toNat := by simp [wordAt, usedCell, MemoryBytes.wordBits]
  have pool : used.toNat + gas.toNat ≤ 16777216 := by
    simp only [regularBudget, wordAt, gasCell, usedCell, MemoryBytes.wordBits] at cap
    omega
  have covers : (MemoryExpansionCost.resultPair start size current).1.toNat ≤ amount.toNat := by
    dsimp only [amount]
    rw [SaturatingAdd.result_nat]
    have bound := (MemoryExpansionCost.resultPair start size current).1.isLt
    omega
  have advance := MemoryExpansionCost.affordable start size current amount used.toNat gas.toNat view.lengthAligned
    (by rw [oldUsed] at covered; exact covered) pool (BitVec.le_def.mp affordable) covers
  rw [suffix_shape] at suffixRun
  have extendSafe : Input.LocalPrefix (ofString "x") (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (localVar "x")]) := .call none _ _ (by simp)
  obtain ⟨expanded, extendRun, returnRun, saved⟩ := extendSafe.normal_continue charged post MemoryExtend.returnZero returned suffixRun
  have extendArgs : evalListHOLFinite charged (h := fun address => Classical.propDecidable (charged.memaddrs address)) [.rfield 1 (localVar "x")] = some [.val (.word expand)] := by
    have cell := xRetained.trans xLocal
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, cell, MemoryExpansionCost.pairValue, expand]
  obtain ⟨extendFits, extendClock, expandedView, budgetSum, usedSum⟩ :=
    MemoryExtend.call_sums charged expanded frame base current capacity pointer scratch expand amount used.toNat [.rfield 1 (localVar "x")]
      chargedView advance extendArgs [] (by simp) (by simp) extendRun
  obtain ⟨_, _, _, _, extendAway⟩ := MemoryExtend.call_normal charged expanded frame base current capacity pointer scratch expand amount used.toNat
    [.rfield 1 (localVar "x")] chargedView advance extendArgs extendRun
  have expandedBudget : regularBudget expanded.memory frame = regularBudget charged.memory frame := by simpa [FrameSums.budget] using budgetSum
  have expandedUsed : (wordAt expanded.memory (frame + 184#64)).toNat = (wordAt charged.memory (frame + 184#64)).toNat := by simpa [FrameSums.used] using usedSum
  obtain ⟨read, postEq⟩ := Input.return_normal expanded post (.const 0#64) returned returnRun
  have value : returned = .val (.word 0#64) := by simpa [eval, evalHOLExact] using (Option.some.inj read).symm
  have postView := expandedView.after_erase (show Input.LocalEffects.erase post = Input.LocalEffects.erase expanded by rw [postEq]; rfl)
  refine ⟨value, ?_, ?_, postView, ?_, ?_, ?_, ?_⟩
  · rw [chargeClock] at extendFits
    change MemoryExtend.price current capacity expand + 2 ≤ source.clock
    omega
  · rw [postEq]
    change expanded.clock = _
    rw [extendClock, chargeClock]
    change source.clock - 1 - (MemoryExtend.price current capacity expand + 1) = source.clock - (MemoryExtend.price current capacity expand + 2)
    omega
  · rw [postEq]
    exact expandedBudget.trans chargeBudget
  · rw [postEq]
    change (wordAt expanded.memory _).toNat = _
    rw [expandedUsed, credit, oldUsed]
  · rw [postEq]
    change (MemoryGasCost.resultWord (current + expand)).toNat ≤ (wordAt expanded.memory _).toNat
    rw [expandedUsed, credit]
    exact advance.covered
  · intro query outside notLength notCapacity notGas notUsed
    rw [postEq]
    change expanded.memory query = _
    rw [extendAway query outside notLength notCapacity]
    exact RegularCharge.call_other_word source charged frame amount query [localVar "total"] chargeArgs
      (OriginalCodeEnvironment.charge_gas source.code view.installed) view.ev cap chargeRun notGas notUsed

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.suffix_shape
#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.after_total_normal
