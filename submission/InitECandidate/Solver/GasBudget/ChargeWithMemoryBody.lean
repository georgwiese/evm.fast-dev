import InitECandidate.Solver.GasBudget.ChargeWithMemoryExpansion

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch fee : BitVec 64) (start size : U256Value.Words)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (baseLocal : source.locals.lookup (ofString "base") = some (.val (.word fee)))
    (startLocal : source.locals.lookup (ofString "start") = some (U256Value.tuple start))
    (sizeLocal : source.locals.lookup (ofString "size") = some (U256Value.tuple size))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ paid : Nat,
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 24 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2) scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (SaturatingAdd.resultWord fee (MemoryExpansionCost.resultPair start size current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat ∧ OutsideEffect source post frame base scratch := by
  have costView : MemoryExpansionCost.View source frame current :=
    ⟨view.installed, view.ev, view.mapped 32 (by simp), view.lengthCell⟩
  obtain ⟨setupPaid, ready, inner, setupPositive, setupBound, setupFits, readyFields, readyClock, xLocal, totalLocal, run, scopeFields, scopeClock⟩ :=
    setup_value source post frame current fee start size costView baseLocal startLocal sizeLocal returned normal
  have readyView := view.after_erase readyFields
  have memory : ready.memory = source.memory := Input.LocalEffects.memory_of_erase source ready readyFields
  have readyCap : regularBudget ready.memory frame ≤ 16777216 := by rw [memory]; exact cap
  have readyCovered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt ready.memory (frame + 184#64)).toNat := by rw [memory]; exact covered
  obtain ⟨value, tailFits, tailClock, innerView, budget, credit, memoryCost, tailAway⟩ :=
    after_total_normal ready inner frame base current capacity pointer scratch fee start size readyView xLocal totalLocal readyCap readyCovered returned run
  let tailPaid := MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 2
  refine ⟨value, setupPaid + tailPaid, by dsimp only [tailPaid]; omega, ?_, ?_, innerView.after_erase scopeFields, ?_, ?_, ?_, ?_⟩
  · rw [readyClock] at tailFits
    change setupPaid + (MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 2) ≤ source.clock
    omega
  · rw [scopeClock, tailClock, readyClock]
    dsimp only [tailPaid]
    omega
  · rw [Input.LocalEffects.memory_of_erase inner post scopeFields, budget, memory]
  · rw [Input.LocalEffects.memory_of_erase inner post scopeFields, credit, memory]
  · rw [Input.LocalEffects.memory_of_erase inner post scopeFields]
    exact memoryCost
  · intro query outside notLength notCapacity notGas notUsed
    rw [Input.LocalEffects.memory_of_erase inner post scopeFields, tailAway query outside notLength notCapacity notGas notUsed, memory]

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.body_normal
