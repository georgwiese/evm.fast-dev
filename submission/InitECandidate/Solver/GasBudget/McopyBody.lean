import InitECandidate.Solver.GasBudget.McopySuffix
import InitECandidate.Solver.GasBudget.StackPopsTripleValues
import InitECandidate.Solver.GasBudget.MemoryExtendPopView

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch mark : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (baseLower : 2701131776 ≤ base.toNat) (scratchUpper : scratch.toNat ≤ 33806089496)
    (markAligned : mark.toNat % 8 = 0) (markUpper : mark.toNat ≤ 33806089496)
    (headerBefore : frame.toNat + 280 ≤ mark.toNat)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (src dst len : U256Value.Words) (paid : Nat),
      mark.toNat + (SatWord.resultWord len).toNat ≤ 33806089496 ∧
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost2.resultPair src len dst len current).2 + guardPrice base mark src dst len + 54 ∧
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost2.resultPair src len dst len current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost2.resultPair src len dst len current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost2.resultPair src len dst len current).2) scratch ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + (chargeWord src dst len current).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost2.resultPair src len dst len current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧
      (wordAt post.memory (frame + 16#64)).toNat + 3 = (wordAt source.memory (frame + 16#64)).toNat ∧
      (∀ query, Arenas.Outside base scratch query → CopyGeneral.Away mark query (SatWord.resultWord len).toNat →
        query ≠ frame + 0#64 → query ≠ frame + 16#64 → query ≠ frame + 32#64 → query ≠ frame + 40#64 →
        query ≠ frame + 64#64 → query ≠ frame + 184#64 → post.memory query = source.memory query) := by
  rw [body_shape] at normal
  obtain ⟨dst, src, len, popped, scopedPost, before, dstCell, srcCell, lenCell, poppedRun, scopeFields, scopeClock, popDepth⟩ :=
    StackPop.triple_normal source post frame "dst" "src" "len" (by decide) (by decide) (by decide) program
      (OriginalCodeEnvironment.stack_pop source.code view.installed) view.ev returned normal
  have poppedView := view.after_pops before
  have poppedCap : regularBudget popped.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
  have poppedCovered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt popped.memory (frame + 184#64)).toNat := by unfold wordAt; rw [before.used]; exact covered
  obtain ⟨prefixPaid, ready, inner, prefixBound, prefixFits, prefixClock, readyView, readySrc, readyDst, readyN,
      prefixBudget, prefixCredit, memoryCost, prefixAway, ranges, globals, mapped, suffixRun, suffixFields, suffixClock⟩ :=
    expansion_prefix popped scopedPost frame base current capacity pointer scratch src dst len poppedView srcCell dstCell lenCell poppedCap poppedCovered returned poppedRun
  have readyHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by rw [globals _ (by decide), before.globals_eq]; exact heapGlobal
  have readyDomain : ready.memaddrs = InitE.ordinaryDomain := by rw [mapped, before.memaddrs_eq]; exact domain
  obtain ⟨result, room, tailFits, tailClock, finalView, finalHeap, tailBudget, tailUsed, tailSP, tailAway⟩ :=
    suffix_normal ready inner frame base _ _ _ scratch mark src dst len readyView readySrc readyDst readyN readyHeap readyDomain
      baseLower scratchUpper markAligned markUpper headerBefore ranges returned suffixRun
  have finalFields := scopeFields.trans suffixFields
  have memory : post.memory = inner.memory := Input.LocalEffects.memory_of_erase inner post finalFields
  refine ⟨result, src, dst, len, 3 + prefixPaid + (guardPrice base mark src dst len + 1), room, by omega, ?_, ?_,
    finalView.after_erase finalFields, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prefixClock, before.clock] at tailFits
    rw [before.clock] at prefixFits
    have funded := before.fits
    omega
  · rw [scopeClock, suffixClock, tailClock, prefixClock, before.clock]
    omega
  · have preserved := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals.lookup (ofString "heap_ptr")) finalFields
    exact preserved.trans finalHeap
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
    exact popDepth
  · intro query outside heapAway notPC notSP notLength notCapacity notGas notUsed
    rw [memory, tailAway query outside heapAway notPC, prefixAway query outside notLength notCapacity notGas notUsed, before.outside query notSP]

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.body_normal
