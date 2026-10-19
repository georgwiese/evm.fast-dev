import InitECandidate.Solver.GasBudget.StackPopsExceptionValues
import InitECandidate.Solver.GasBudget.RevertSuffix
import InitECandidate.Solver.GasBudget.RevertExpansionPrefix
import InitECandidate.Solver.GasBudget.MemoryExtendPopView

namespace InitECandidate.Solver.GasBudget.RevertOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem body_exception1 (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch sp : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (normal : evaluateHOLFiniteState source body = (some (.exception (ofString "EvmErr") (.val (.word 1#64))), post)) :
    ∃ (start size : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 27 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + (MemoryExpansionCost.resultPair start size current).1.toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧
      (wordAt post.memory (frame + 16#64)).toNat + 2 = (wordAt source.memory (frame + 16#64)).toNat ∧
      post.memory (frame + 104#64) = source.memory (frame + 104#64) ∧
      (∀ key, key ≠ ofString "frame_mem_ptr" → post.globals.lookup key = source.globals.lookup key) ∧
      (U256Zero.resultWord size = 0#64 → (SatWord.resultWord start).toNat + (SatWord.resultWord size).toNat ≤
        (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2).toNat) ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 16#64 → query ≠ frame + 32#64 →
        query ≠ frame + 40#64 → query ≠ frame + 64#64 → query ≠ frame + 184#64 → query ≠ frame + 120#64 →
        query ≠ frame + 128#64 → post.memory query = source.memory query) := by
  rw [body_shape] at normal
  obtain ⟨start, size, popped, scopedPost, before, startCell, sizeCell, poppedRun, scopeFields, scopeClock, popDepth⟩ :=
    StackPop.pair_exception_values source post frame sp "start" "size" (by decide) program
      (OriginalCodeEnvironment.stack_pop source.code view.installed) view.ev spMapped spCell shape (ofString "EvmErr") (.val (.word 1#64)) (by simp only [ne_eq, ValueHOL.val.injEq, HolWordLab.word.injEq]; decide) normal
  have poppedView := view.after_pops before
  have poppedCap : regularBudget popped.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
  have poppedCovered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt popped.memory (frame + 184#64)).toNat := by unfold wordAt; rw [before.used]; exact covered
  obtain ⟨prefixPaid, ready, inner, prefixBound, prefixFits, prefixClock, readyView, readyStart, readySize, prefixBudget,
      prefixCredit, memoryCost, prefixAway, range, globals, mapped, shapes, suffixRun, suffixFields, suffixClock⟩ :=
    expansion_prefix popped scopedPost frame base current capacity pointer scratch start size poppedView startCell sizeCell poppedCap poppedCovered (.val (.word 1#64)) (by simp only [ne_eq, ValueHOL.val.injEq, HolWordLab.word.injEq]; decide) poppedRun
  have readyShape : ready.eshapes.lookup (ofString "EvmErr") = some .one := by rw [shapes, before.eshapes_eq]; exact shape
  obtain ⟨tailFits, actualId, actualPayload, tailClock, finalView, tailGlobals, tailBudget, tailUsed, tailSP, tailMemory, tailAway⟩ :=
    suffix_exception ready inner frame base _ _ _ scratch start size readyView readyStart readySize readyShape (ofString "EvmErr") (.val (.word 1#64)) suffixRun
  have finalFields := scopeFields.trans suffixFields
  have memory : post.memory = inner.memory := Input.LocalEffects.memory_of_erase inner post finalFields
  refine ⟨start, size, 2 + prefixPaid + 2, by omega, ?_, ?_, finalView.after_erase finalFields, ?_, ?_, ?_, ?_,
    ?_, ?_, range, ?_⟩
  · rw [prefixClock, before.clock] at tailFits
    rw [before.clock] at prefixFits
    have funded := before.fits
    omega
  · rw [scopeClock, suffixClock, tailClock, prefixClock, before.clock]
    omega
  · rw [memory, tailBudget, prefixBudget, before.budget]
  · unfold wordAt
    rw [memory, tailUsed]
    change (wordAt ready.memory _).toNat = _
    rw [prefixCredit]
    unfold wordAt
    rw [before.used]
  · rw [memory]
    change _ ≤ (MemoryBytes.wordBits (inner.memory (frame + 184#64))).toNat
    rw [tailUsed]
    exact memoryCost
  · unfold wordAt
    rw [memory, tailSP, prefixAway _ (view.header_outside 16 (by decide)) (offsets_ne frame _ _ (by decide))
      (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))]
    simpa only [wordAt, spCell, MemoryBytes.wordBits] using popDepth
  · rw [memory, tailAway _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide)),
      prefixAway _ (view.header_outside 104 (by decide)) (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))
        (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide)),
      before.outside _ (offsets_ne frame _ _ (by decide))]
  · intro key different
    have preserved := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals.lookup key) finalFields
    change post.globals.lookup key = inner.globals.lookup key at preserved
    rw [preserved, tailGlobals, globals key different, before.globals_eq]
  · intro query outside notSP notLength notCapacity notGas notUsed notOutput notSize
    rw [memory, tailAway query notOutput notSize, prefixAway query outside notLength notCapacity notGas notUsed, before.outside query notSP]

end InitECandidate.Solver.GasBudget.RevertOpcode

#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.body_exception1
