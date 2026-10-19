import InitECandidate.Solver.GasBudget.ReturnProgram
import InitECandidate.Solver.GasBudget.MemoryExpansionCostPrefix

namespace InitECandidate.Solver.GasBudget.ReturnOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

set_option maxHeartbeats 1000000 in
theorem expansion_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64) (start size : U256Value.Words)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (startLocal : source.locals.lookup (ofString "start") = some (U256Value.tuple start))
    (sizeLocal : source.locals.lookup (ofString "size") = some (U256Value.tuple size))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source program = (some (.returned returned), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 23 ∧ paid ≤ source.clock ∧
      ready.clock = source.clock - paid ∧
      MemoryExtend.View ready frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2) scratch ∧
      ready.locals.lookup (ofString "start") = some (U256Value.tuple start) ∧
      ready.locals.lookup (ofString "size") = some (U256Value.tuple size) ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + (MemoryExpansionCost.resultPair start size current).1.toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)).toNat ≤
        (wordAt ready.memory (frame + 184#64)).toNat ∧ ChargeWithMemory.OutsideEffect source ready frame base scratch ∧
      (U256Zero.resultWord size = 0#64 → (SatWord.resultWord start).toNat + (SatWord.resultWord size).toNat ≤
        (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2).toNat) ∧
      (∀ key, key ≠ ofString "frame_mem_ptr" → ready.globals.lookup key = source.globals.lookup key) ∧
      ready.memaddrs = source.memaddrs ∧
      evaluateHOLFiniteState ready afterExpansion = (some (.returned returned), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  have costView : MemoryExpansionCost.View source frame current := ⟨view.installed, view.ev, view.mapped 32 (by simp), view.lengthCell⟩
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "start", localVar "size"] = some [U256Value.tuple start, U256Value.tuple size] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, startLocal, sizeLocal]
  obtain ⟨costPaid, first, firstPost, positive, bound, funded, firstEq, fields, run, scopeEq⟩ :=
    MemoryExpansionCost.normal_prefix source post frame current start size costView "x" [localVar "start", localVar "size"] afterCost returned args normal
  have firstView := view.after_erase fields
  have memory := Input.LocalEffects.memory_of_erase source first fields
  have firstCap : regularBudget first.memory frame ≤ 16777216 := by rw [memory]; exact cap
  have firstCovered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt first.memory (frame + 184#64)).toNat := by rw [memory]; exact covered
  have xCell := Input.KnownUnaryPrefix.lookup_same firstEq
  have chargeArgs : evalListHOLFinite first (h := fun address => Classical.propDecidable (first.memaddrs address)) [.rfield 0 (localVar "x")] =
      some [.val (.word (MemoryExpansionCost.resultPair start size current).1)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, xCell, MemoryExpansionCost.pairValue]
  obtain ⟨ready, tailFits, tailClock, locals, readyView, budget, credit, memoryCost, away, range, globals, domain, tailRun⟩ :=
    MemoryExpansionCost.charged_normal first firstPost frame base current capacity pointer scratch (MemoryExpansionCost.resultPair start size current).1 start size
      firstView xCell firstCap firstCovered (Nat.le_refl _) [.rfield 0 (localVar "x")] chargeArgs afterExpansion returned run
  have firstClock : first.clock = source.clock - costPaid := by rw [firstEq]; rfl
  let tailPaid := MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 2
  refine ⟨costPaid + tailPaid, ready, firstPost, by dsimp only [tailPaid]; omega, ?_, ?_, readyView, ?_, ?_, ?_, ?_, memoryCost, ?_, range, ?_, ?_, tailRun, ?_, ?_⟩
  · rw [firstClock] at tailFits
    dsimp only [tailPaid]
    omega
  · rw [tailClock, firstClock]
    dsimp only [tailPaid]
    omega
  · rw [locals]
    exact (Input.KnownUnaryPrefix.lookup_other firstEq "start" (by decide)).trans startLocal
  · rw [locals]
    exact (Input.KnownUnaryPrefix.lookup_other firstEq "size" (by decide)).trans sizeLocal
  · rw [budget, memory]
  · rw [credit, memory]
  · intro query outside notLength notCapacity notGas notUsed
    rw [away query outside notLength notCapacity notGas notUsed, memory]
  · intro key different
    rw [globals key different, firstEq]; rfl
  · rw [domain, firstEq]; rfl
  · rw [scopeEq]; rfl
  · rw [scopeEq]; rfl

end InitECandidate.Solver.GasBudget.ReturnOpcode

#print axioms InitECandidate.Solver.GasBudget.ReturnOpcode.expansion_prefix
