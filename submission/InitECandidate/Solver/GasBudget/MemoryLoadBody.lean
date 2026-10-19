import InitECandidate.Solver.GasBudget.MemoryLoadSuffix
import InitECandidate.Solver.GasBudget.StackPopValue
import InitECandidate.Solver.GasBudget.MemoryExtendPopView
import InitECandidate.Solver.GasBudget.ChargeWithMemoryCall
import InitECandidate.Solver.GasBudget.DirectStackFootprint

namespace InitECandidate.Solver.GasBudget.MemoryLoad
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

def size32 : U256Value.Words := fun index => if index.val = 0 then 32#64 else 0#64

def Footprint (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch stack sp : BitVec 64) : Prop :=
  ∀ query, Arenas.Outside base scratch query → query ≠ frame + 0#64 → query ≠ frame + 16#64 →
    query ≠ frame + 32#64 → query ≠ frame + 40#64 → query ≠ frame + 64#64 → query ≠ frame + 184#64 →
    (∀ index < 4, query ≠ (stack + BitVec.ofNat 64 (sp.toNat - 1) * 32#64) + BitVec.ofNat 64 (8 * index)) →
    post.memory query = source.memory query

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (entry : DirectStackOpcode.Entry source frame)
    (owned : DirectStackOpcode.HeaderApart frame entry.base entry.capacity.toNat)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source MemoryOpcode.Kind.mload.body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (start : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size32 current).2 + 62 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size32 current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size32 current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size32 current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord 3#64 (MemoryExpansionCost.resultPair start size32 current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size32 current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧
      (wordAt post.memory (frame + 16#64)).toNat = entry.sp.toNat ∧ 1 ≤ entry.sp.toNat ∧ Footprint source post frame base scratch entry.base entry.sp := by
  rw [MemoryOpcode.body_shape] at normal
  obtain ⟨start, popped, scopedPost, before, startLocal, poppedRun, scopeFields, scopeClock, popDepth⟩ :=
    StackPop.value_normal source post frame "start" _ entry.popCode entry.ev returned normal
  have poppedView := view.after_pops before
  have poppedCap : regularBudget popped.memory frame ≤ 16777216 := by rw [before.budget]; exact entry.gasCap
  have poppedCovered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt popped.memory (frame + 184#64)).toNat := by
    unfold wordAt
    rw [before.used]
    exact covered
  have safe : Input.LocalPrefix (ofString "start") (.call (some (none, none)) (ofString "charge_with_memory") MemoryOpcode.Kind.mload.arguments) := .call none _ _ (by simp)
  obtain ⟨charged, chargeRun, suffixRun, retained⟩ := safe.normal_continue popped scopedPost MemoryOpcode.Kind.mload.suffix returned poppedRun
  have args : evalListHOLFinite popped (h := fun address => Classical.propDecidable (popped.memaddrs address)) MemoryOpcode.Kind.mload.arguments =
      some [.val (.word 3#64), U256Value.tuple start, U256Value.tuple size32] := by
    simp [MemoryOpcode.Kind.arguments, MemoryOpcode.Kind.size, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact,
      localVar, startLocal, size32, U256Value.tuple]
  obtain ⟨chargePaid, chargeBound, chargeFits, chargeClock, chargedView, chargeBudget, chargeCredit, memoryCost, chargeAway⟩ :=
    ChargeWithMemory.call_normal popped charged frame base current capacity pointer scratch 3#64 start size32 MemoryOpcode.Kind.mload.arguments poppedView args poppedCap poppedCovered chargeRun
  let sp := wordAt popped.memory (frame + 16#64)
  have popNumber : sp.toNat + 1 = entry.sp.toNat := by simpa only [sp, wordAt, entry.spCell, MemoryBytes.wordBits] using popDepth
  have room : sp < entry.capacity := by
    apply BitVec.lt_def.mpr
    have bounded := entry.depthBound
    omega
  have header (offset : Nat) (high : offset ≤ 272) (notLength : BitVec.ofNat 64 offset ≠ 32#64)
      (notCapacity : BitVec.ofNat 64 offset ≠ 40#64) (notGas : BitVec.ofNat 64 offset ≠ 64#64)
      (notUsed : BitVec.ofNat 64 offset ≠ 184#64) : charged.memory (frame + BitVec.ofNat 64 offset) = popped.memory (frame + BitVec.ofNat 64 offset) :=
    chargeAway _ (view.header_outside offset high) (offsets_ne frame _ _ notLength) (offsets_ne frame _ _ notCapacity)
      (offsets_ne frame _ _ notGas) (offsets_ne frame _ _ notUsed)
  have spCell : charged.memory (frame + 16#64) = .word sp := (header 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (memory_word _ _)
  have capCell : charged.memory (frame + 232#64) = .word entry.capacity :=
    (header 232 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((before.outside _ (offsets_ne frame 232#64 16#64 (by decide))).trans entry.capCell)
  have baseCell : charged.memory (frame + 8#64) = .word entry.base :=
    (header 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((before.outside _ (offsets_ne frame 8#64 16#64 (by decide))).trans entry.baseCell)
  have chargeDomain := (Input.evaluation_fields popped charged _ none chargeRun).1
  have chargedCap : regularBudget charged.memory frame ≤ 16777216 := by rw [chargeBudget, before.budget]; exact entry.gasCap
  let chargedEntry : DirectStackOpcode.Entry charged frame :=
    ⟨entry.base, sp, entry.capacity, chargedView.ev,
      OriginalCodeEnvironment.stack_pop charged.code chargedView.installed,
      OriginalCodeEnvironment.charge_gas charged.code chargedView.installed,
      OriginalCodeEnvironment.stack_push charged.code chargedView.installed,
      OriginalCodeEnvironment.pc_add charged.code chargedView.installed,
      spCell, capCell, by rw [chargeDomain, before.memaddrs_eq]; exact entry.baseMapped,
      baseCell, by have bound := BitVec.lt_def.mp room; omega, entry.capBound, chargedCap, entry.separate⟩
  have memoryApart : ∀ offset ∈ ([24, 32, 40] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (chargedEntry.base + chargedEntry.sp * 32#64) + BitVec.ofNat 64 (8 * index) := by
    intro offset member index inside
    have high : offset < 280 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    have actual := owned sp.toNat (BitVec.lt_def.mp room) offset high index inside
    simpa only [chargedEntry, BitVec.ofNat_toNat, BitVec.setWidth_eq] using actual
  obtain ⟨value, suffixPaid, suffixBound, suffixFits, suffixClock, finalView, suffixBudget, suffixUsed, finalSP, finalDepth, suffixAway⟩ :=
    suffix_normal charged scopedPost frame base _ _ _ scratch start chargedView chargedEntry room memoryApart (retained.trans startLocal) returned suffixRun
  have memory : post.memory = scopedPost.memory := Input.LocalEffects.memory_of_erase scopedPost post scopeFields
  refine ⟨value, start, 1 + chargePaid + suffixPaid, by omega, ?_, ?_, finalView.after_erase scopeFields, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · rw [chargeClock, before.clock] at suffixFits
    rw [before.clock] at chargeFits
    have fits := before.fits
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
  · rw [memory, finalDepth]
    exact popNumber
  · have spEq : sp = BitVec.ofNat 64 (entry.sp.toNat - 1) := by
      have number : sp.toNat = entry.sp.toNat - 1 := by omega
      rw [← number]
      simp
    intro query outside notPC notSP notLength notCapacity notGas notUsed notSlot
    rw [memory, suffixAway query notPC notSP (by simpa only [chargedEntry, spEq] using notSlot),
      chargeAway query outside notLength notCapacity notGas notUsed, before.outside query notSP]

end InitECandidate.Solver.GasBudget.MemoryLoad

#print axioms InitECandidate.Solver.GasBudget.MemoryLoad.body_normal
