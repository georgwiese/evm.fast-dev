import InitECandidate.Solver.GasBudget.MemoryLoadBody
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.GasBudget.MemoryLoad
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix Input.RlpWrite

theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (entry : DirectStackOpcode.Entry source frame)
    (owned : DirectStackOpcode.HeaderApart frame entry.base entry.capacity.toNat)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_mload") []) = (none, post)) :
    ∃ (start : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size32 current).2 + 63 ∧ paid ≤ source.clock ∧
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
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "op_mload") [] normal
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "op_mload") [] MemoryOpcode.Kind.mload.body .one
    (MemoryOpcode.original_code .mload source.code view.installed) values actual callee shape called
  rw [bodyEq] at bodyRun
  have entryView : MemoryExtend.View (callEntryStateHOLFinite source callee) frame base current capacity pointer scratch := view.after_erase rfl
  let incoming := entry.call_entry source frame callee
  obtain ⟨value, start, paid, bound, funded, clock, targetView, budget, credit, memoryCost, depth, nonzero, away⟩ :=
    body_normal (callEntryStateHOLFinite source callee) target frame base current capacity pointer scratch entryView incoming owned covered returned bodyRun
  change paid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - paid at clock
  refine ⟨start, paid + 1, by omega, by omega, ?_, targetView.after_erase (by rw [postEq]; rfl), ?_, ?_, ?_, ?_, nonzero, ?_⟩
  · rw [postEq]
    change target.clock = _
    rw [clock]
    omega
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact memoryCost
  · rw [postEq]; exact depth
  · rw [postEq]
    exact away

end InitECandidate.Solver.GasBudget.MemoryLoad

#print axioms InitECandidate.Solver.GasBudget.MemoryLoad.call_normal
