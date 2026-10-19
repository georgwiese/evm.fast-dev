import InitECandidate.Solver.GasBudget.DispatchNormal
import InitECandidate.Solver.GasBudget.MemoryLoadCall

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix Input.RlpWrite

theorem selection_load : tree.choose 81#64 = .invoke "op_mload" [] := by rfl

theorem load_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (entry : DirectStackOpcode.Entry source frame)
    (owned : DirectStackOpcode.HeaderApart frame entry.base entry.capacity.toNat)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 81#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ (start : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2 + 63 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord 3#64 (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧
      (wordAt post.memory (frame + 16#64)).toNat = entry.sp.toNat ∧ 1 ≤ entry.sp.toNat ∧ MemoryLoad.Footprint source post frame base scratch entry.base entry.sp := by
  obtain ⟨result, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post 81#64 opLocal returned normal
  rw [selection_load] at selected
  cases selected
  obtain ⟨start, paid, bound, funded, clock, middleView, budget, credit, memoryCost, depth, nonzero, away⟩ :=
    MemoryLoad.call_normal source middle frame base current capacity pointer scratch view entry owned covered helperRun
  refine ⟨start, paid, bound, funded, ?_, middleView.after_erase (by rw [postEq]; rfl), ?_, ?_, ?_, ?_, nonzero, ?_⟩
  · rw [postEq]; exact clock
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact memoryCost
  · rw [postEq]; exact depth
  · rw [postEq]; exact away

theorem load_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (entry : DirectStackOpcode.Entry source frame)
    (owned : DirectStackOpcode.HeaderApart frame entry.base entry.capacity.toNat)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word 81#64)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, post)) :
    ∃ (start : U256Value.Words) (paid : Nat),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2 + 64 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord 3#64 (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start MemoryLoad.size32 current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧
      (wordAt post.memory (frame + 16#64)).toNat = entry.sp.toNat ∧ 1 ≤ entry.sp.toNat ∧ MemoryLoad.Footprint source post frame base scratch entry.base entry.sp := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "op_dispatch") arguments normal
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨argument, argumentsEq, bodyEq, shapeEq, typed, binding⟩ :=
    Input.CallNormal.unary_lookup_data source.code.lookup (ofString "op_dispatch") (ofString "op") .one body .one
      (OriginalCodeEnvironment.op_dispatch source.code view.installed) [.val (.word 81#64)] actual callee shape called
  have argumentEq : argument = .val (.word 81#64) := (List.cons.inj argumentsEq).1.symm
  rw [argumentEq] at binding
  rw [bodyEq] at bodyRun
  have entryView : MemoryExtend.View (callEntryStateHOLFinite source callee) frame base current capacity pointer scratch := view.after_erase rfl
  let incoming := entry.call_entry source frame callee
  obtain ⟨start, paid, bound, funded, clock, targetView, budget, credit, memoryCost, depth, nonzero, away⟩ :=
    load_body_normal (callEntryStateHOLFinite source callee) target frame base current capacity pointer scratch entryView incoming owned covered binding returned bodyRun
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
  · rw [postEq]; exact away

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_load
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.load_body_normal
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.load_call_normal
