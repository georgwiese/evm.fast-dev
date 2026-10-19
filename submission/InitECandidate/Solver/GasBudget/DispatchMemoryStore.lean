import InitECandidate.Solver.GasBudget.DispatchNormal
import InitECandidate.Solver.GasBudget.MemoryStoreCall

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix Input.RlpWrite

 theorem selection_store : tree.choose 82#64 = .invoke "op_mstore" [] := by rfl

theorem store_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 82#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ (start : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2 + 43 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord 3#64 (MemoryExpansionCost.resultPair start MemoryStore.size32 current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧
      (wordAt post.memory (frame + 16#64)).toNat + 2 = (wordAt source.memory (frame + 16#64)).toNat ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 0#64 → query ≠ frame + 16#64 →
        query ≠ frame + 32#64 → query ≠ frame + 40#64 → query ≠ frame + 64#64 → query ≠ frame + 184#64 →
        post.memory query = source.memory query) := by
  obtain ⟨result, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post 82#64 opLocal returned normal
  rw [selection_store] at selected
  cases selected
  obtain ⟨start, paid, bound, funded, clock, middleView, budget, credit, memoryCost, depth, away⟩ :=
    MemoryStore.call_normal source middle frame base current capacity pointer scratch view cap covered helperRun
  refine ⟨start, paid, bound, funded, ?_, middleView.after_erase (by rw [postEq]; rfl), ?_, ?_, ?_, ?_, ?_⟩
  · rw [postEq]; exact clock
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact memoryCost
  · rw [postEq]; exact depth
  · intro query outside notPC notSP notLength notCapacity notGas notUsed
    rw [postEq]
    exact away query outside notPC notSP notLength notCapacity notGas notUsed

theorem store_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64) (arguments : List (ExpHOL 64))
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word 82#64)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, post)) :
    ∃ (start : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2 + 44 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord 3#64 (MemoryExpansionCost.resultPair start MemoryStore.size32 current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧
      (wordAt post.memory (frame + 16#64)).toNat + 2 = (wordAt source.memory (frame + 16#64)).toNat ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 0#64 → query ≠ frame + 16#64 →
        query ≠ frame + 32#64 → query ≠ frame + 40#64 → query ≠ frame + 64#64 → query ≠ frame + 184#64 →
        post.memory query = source.memory query) := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "op_dispatch") arguments normal
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨argument, argumentsEq, bodyEq, shapeEq, typed, binding⟩ :=
    Input.CallNormal.unary_lookup_data source.code.lookup (ofString "op_dispatch") (ofString "op") .one body .one
      (OriginalCodeEnvironment.op_dispatch source.code view.installed) [.val (.word 82#64)] actual callee shape called
  have argumentEq : argument = .val (.word 82#64) := (List.cons.inj argumentsEq).1.symm
  rw [argumentEq] at binding
  rw [bodyEq] at bodyRun
  have entryView : MemoryExtend.View (callEntryStateHOLFinite source callee) frame base current capacity pointer scratch := view.after_erase rfl
  obtain ⟨start, paid, bound, funded, clock, targetView, budget, credit, memoryCost, depth, away⟩ :=
    store_body_normal (callEntryStateHOLFinite source callee) target frame base current capacity pointer scratch entryView cap covered binding returned bodyRun
  change paid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - paid at clock
  refine ⟨start, paid + 1, by omega, by omega, ?_, targetView.after_erase (by rw [postEq]; rfl), ?_, ?_, ?_, ?_, ?_⟩
  · rw [postEq]
    change target.clock = _
    rw [clock]
    omega
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact memoryCost
  · rw [postEq]; exact depth
  · intro query outside notPC notSP notLength notCapacity notGas notUsed
    rw [postEq]
    exact away query outside notPC notSP notLength notCapacity notGas notUsed

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_store
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.store_body_normal
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.store_call_normal
