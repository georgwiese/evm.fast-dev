import InitECandidate.Solver.GasBudget.ChargeWithMemoryBody
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

theorem lookup_known (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (installed : Input.OriginalCode.Installed code) (fee : BitVec 64) (start size : U256Value.Words)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite code.lookup (ofString "charge_with_memory") [.val (.word fee), U256Value.tuple start, U256Value.tuple size] = some (actual, callee, shape)) :
    actual = body ∧ callee.lookup (ofString "base") = some (.val (.word fee)) ∧
      callee.lookup (ofString "start") = some (U256Value.tuple start) ∧ callee.lookup (ofString "size") = some (U256Value.tuple size) := by
  have raw := lookupCodeHOLFinite_eq_some code.lookup (ofString "charge_with_memory") _ actual callee shape called
  simp only [lookupCodeHOLExact, original_code code installed] at raw
  split at raw
  · have same := Option.some.inj raw
    have actualEq := congrArg Prod.fst same
    have baseEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "base")) same
    have startEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "start")) same
    have sizeEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "size")) same
    exact ⟨actualEq.symm, by simpa [ofString] using baseEq.symm, by simpa [ofString] using startEq.symm, by simpa [ofString] using sizeEq.symm⟩
  · cases raw

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch fee : BitVec 64) (start size : U256Value.Words) (arguments : List (ExpHOL 64))
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word fee), U256Value.tuple start, U256Value.tuple size])
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_with_memory") arguments) = (none, post)) :
    ∃ paid : Nat, paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 25 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord fee (MemoryExpansionCost.resultPair start size current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧ OutsideEffect source post frame base scratch := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "charge_with_memory") arguments normal
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨bodyEq, baseLocal, startLocal, sizeLocal⟩ := lookup_known source.code view.installed fee start size actual callee shape called
  rw [bodyEq] at bodyRun
  have entryView : MemoryExtend.View (callEntryStateHOLFinite source callee) frame base current capacity pointer scratch := view.after_erase rfl
  obtain ⟨value, paid, bound, funded, clock, targetView, budget, credit, memoryCost, away⟩ :=
    body_normal (callEntryStateHOLFinite source callee) target frame base current capacity pointer scratch fee start size entryView baseLocal startLocal sizeLocal cap covered returned bodyRun
  change paid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - paid at clock
  refine ⟨paid + 1, by omega, by omega, ?_, targetView.after_erase (by rw [postEq]; rfl), ?_, ?_, ?_, ?_⟩
  · rw [postEq]
    change target.clock = _
    rw [clock]
    omega
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact memoryCost
  · intro query outside notLength notCapacity notGas notUsed
    rw [postEq]
    exact away query outside notLength notCapacity notGas notUsed

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.lookup_known
#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.call_normal
