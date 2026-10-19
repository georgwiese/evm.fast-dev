import InitECandidate.Solver.GasBudget.MemoryStoreSuffix
import InitECandidate.Solver.GasBudget.StackPopsValues
import InitECandidate.Solver.GasBudget.MemoryExtendPopView
import InitECandidate.Solver.GasBudget.ChargeWithMemoryRange

namespace InitECandidate.Solver.GasBudget.MemoryStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

def size32 : U256Value.Words := fun index => if index.val = 0 then 32#64 else 0#64

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source MemoryOpcode.Kind.mstore.body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (start : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size32 current).2 + 42 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size32 current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size32 current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size32 current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord 3#64 (MemoryExpansionCost.resultPair start size32 current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size32 current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧
      (wordAt post.memory (frame + 16#64)).toNat + 2 = (wordAt source.memory (frame + 16#64)).toNat ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 0#64 → query ≠ frame + 16#64 →
        query ≠ frame + 32#64 → query ≠ frame + 40#64 → query ≠ frame + 64#64 → query ≠ frame + 184#64 →
        post.memory query = source.memory query) := by
  rw [MemoryOpcode.body_shape] at normal
  obtain ⟨start, value, popped, scopedPost, before, startLocal, valueLocal, poppedRun, scopeFields, scopeClock, popDepth⟩ :=
    StackPop.pair_normal source post frame "start" "value" (by decide) _
      (OriginalCodeEnvironment.stack_pop source.code view.installed) view.ev returned normal
  have poppedView := view.after_pops before
  have poppedCap : regularBudget popped.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
  have poppedCovered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt popped.memory (frame + 184#64)).toNat := by
    unfold wordAt
    rw [before.used]
    exact covered
  have safe : Input.LocalPrefix (ofString "start") (.call (some (none, none)) (ofString "charge_with_memory") MemoryOpcode.Kind.mstore.arguments) := .call none _ _ (by simp)
  obtain ⟨charged, chargeRun, suffixRun, startRetained⟩ := safe.normal_continue popped scopedPost MemoryOpcode.Kind.mstore.suffix returned poppedRun
  have valueRetained : charged.locals.lookup (ofString "value") = popped.locals.lookup (ofString "value") := by
    have safeValue : Input.LocalPrefix (ofString "value") (.call (some (none, none)) (ofString "charge_with_memory") MemoryOpcode.Kind.mstore.arguments) := .call none _ _ (by simp)
    have info := (safeValue.summary popped).1
    rw [chargeRun] at info
    exact info rfl
  have args : evalListHOLFinite popped (h := fun address => Classical.propDecidable (popped.memaddrs address)) MemoryOpcode.Kind.mstore.arguments = some [.val (.word 3#64), U256Value.tuple start, U256Value.tuple size32] := by
    simp [MemoryOpcode.Kind.arguments, MemoryOpcode.Kind.size, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact,
      localVar, startLocal, size32, U256Value.tuple]
  obtain ⟨chargePaid, chargeBound, chargeFits, chargeClock, chargedView, chargeBudget, chargeCredit, memoryCost, chargeAway⟩ :=
    ChargeWithMemory.call_normal popped charged frame base current capacity pointer scratch 3#64 start size32 MemoryOpcode.Kind.mstore.arguments poppedView args poppedCap poppedCovered chargeRun
  have nonempty : U256Zero.resultWord size32 = 0#64 := by decide
  have range := ChargeWithMemory.call_range popped charged frame base current capacity pointer scratch 3#64 start size32 MemoryOpcode.Kind.mstore.arguments poppedView args poppedCap poppedCovered nonempty chargeRun
  have scalarSize : SatWord.resultWord size32 = 32#64 := by decide
  rw [scalarSize] at range
  change (SatWord.resultWord start).toNat + 32 ≤ _ at range
  obtain ⟨result, suffixPaid, suffixBound, suffixFits, suffixClock, finalView, suffixBudget, suffixUsed, suffixAway⟩ :=
    suffix_normal charged scopedPost frame base _ _ _ scratch start value chargedView (startRetained.trans startLocal) (valueRetained.trans valueLocal) range returned suffixRun
  have memory : post.memory = scopedPost.memory := Input.LocalEffects.memory_of_erase scopedPost post scopeFields
  refine ⟨result, start, 2 + chargePaid + suffixPaid, by omega, ?_, ?_, finalView.after_erase scopeFields, ?_, ?_, ?_, ?_, ?_⟩
  · rw [chargeClock, before.clock] at suffixFits
    have fits := before.fits
    rw [before.clock] at chargeFits
    omega
  · rw [scopeClock, suffixClock, chargeClock, before.clock]
    omega
  · rw [memory, suffixBudget, chargeBudget, before.budget]
  · unfold wordAt
    rw [memory, suffixUsed]
    change (wordAt charged.memory _).toNat = _
    rw [chargeCredit]
    unfold wordAt
    rw [before.used]
  · rw [memory]
    change _ ≤ (MemoryBytes.wordBits (scopedPost.memory (frame + 184#64))).toNat
    rw [suffixUsed]
    exact memoryCost
  · unfold wordAt
    rw [memory, suffixAway _ (view.header_outside 16 (by decide)) (offsets_ne frame _ _ (by decide)),
      chargeAway _ (view.header_outside 16 (by decide)) (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))
        (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))]
    exact popDepth
  · intro query outside notPC notSP notLength notCapacity notGas notUsed
    rw [memory, suffixAway query outside notPC, chargeAway query outside notLength notCapacity notGas notUsed, before.outside query notSP]

end InitECandidate.Solver.GasBudget.MemoryStore

#print axioms InitECandidate.Solver.GasBudget.MemoryStore.body_normal
