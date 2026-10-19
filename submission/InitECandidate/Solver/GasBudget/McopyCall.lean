import InitECandidate.Solver.GasBudget.McopyBody
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix Input.RlpWrite

theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch mark : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (baseLower : 2701131776 ≤ base.toNat) (scratchUpper : scratch.toNat ≤ 33806089496)
    (markAligned : mark.toNat % 8 = 0) (markUpper : mark.toNat ≤ 33806089496)
    (headerBefore : frame.toNat + 280 ≤ mark.toNat)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_mcopy") []) = (none, post)) :
    ∃ (src dst len : U256Value.Words) (paid : Nat),
      mark.toNat + (SatWord.resultWord len).toNat ≤ 33806089496 ∧
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost2.resultPair src len dst len current).2 + guardPrice base mark src dst len + 55 ∧
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
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "op_mcopy") [] normal
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "op_mcopy") [] body .one
    (original_code source.code view.installed) values actual callee shape called
  rw [bodyEq] at bodyRun
  have entryView : MemoryExtend.View (callEntryStateHOLFinite source callee) frame base current capacity pointer scratch := view.after_erase rfl
  obtain ⟨value, src, dst, len, paid, room, bound, funded, clock, targetView, heap, budget, credit, memoryCost, depth, away⟩ :=
    body_normal (callEntryStateHOLFinite source callee) target frame base current capacity pointer scratch mark entryView heapGlobal domain
      baseLower scratchUpper markAligned markUpper headerBefore cap covered returned bodyRun
  change paid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - paid at clock
  refine ⟨src, dst, len, paid + 1, room, by omega, by omega, ?_, targetView.after_erase (by rw [postEq]; rfl), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [postEq]
    change target.clock = _
    rw [clock]
    omega
  · rw [postEq]; exact heap
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact memoryCost
  · rw [postEq]; exact depth
  · intro query outside heapAway notPC notSP notLength notCapacity notGas notUsed
    rw [postEq]
    exact away query outside heapAway notPC notSP notLength notCapacity notGas notUsed

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.call_normal
