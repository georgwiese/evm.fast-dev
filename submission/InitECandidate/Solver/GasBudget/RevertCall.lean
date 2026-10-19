import InitECandidate.Solver.GasBudget.RevertBody
import InitECandidate.Solver.Input.IgnoredCallException

namespace InitECandidate.Solver.GasBudget.RevertOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix Input.RlpWrite

theorem call_exception1 (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch sp : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_revert") []) = (some (.exception (ofString "EvmErr") (.val (.word 1#64))), post)) :
    ∃ (start size : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 28 ∧ paid ≤ source.clock ∧
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
  obtain ⟨positive, values, actual, callee, returnShape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post (ofString "op_revert") [] (ofString "EvmErr") (.val (.word 1#64)) normal
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "op_revert") [] body .one
    (original_code source.code view.installed) values actual callee returnShape called
  rw [bodyEq] at bodyRun
  have entryView : MemoryExtend.View (callEntryStateHOLFinite source callee) frame base current capacity pointer scratch := view.after_erase rfl
  obtain ⟨start, size, paid, bound, funded, clock, targetView, budget, credit, memoryCost, depth, running, globals, range, away⟩ :=
    body_exception1 (callEntryStateHOLFinite source callee) target frame base current capacity pointer scratch sp entryView cap covered spMapped spCell shape bodyRun
  change paid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - paid at clock
  refine ⟨start, size, paid + 1, by omega, by omega, ?_, targetView.after_erase (by rw [postEq]; rfl), ?_, ?_, ?_, ?_, ?_, ?_, range, ?_⟩
  · rw [postEq]
    change target.clock = _
    rw [clock]
    omega
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact memoryCost
  · rw [postEq]; exact depth
  · rw [postEq]; exact running
  · intro key different
    rw [postEq]
    exact globals key different
  · intro query outside notSP notLength notCapacity notGas notUsed notOutput notSize
    rw [postEq]
    exact away query outside notSP notLength notCapacity notGas notUsed notOutput notSize

end InitECandidate.Solver.GasBudget.RevertOpcode

#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.call_exception1
