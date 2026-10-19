import InitECandidate.Solver.GasBudget.McopyValueSetup
import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Charged

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

def afterExpansion : ProgHOL 64 := match suffix with | .seq _ rest => rest | _ => .skip

theorem afterFee_shape : afterFee = MemoryExpansionCost2.chargedProgram [localVar "cost"] afterExpansion := by
  simp only [afterFee, MemoryExpansionCost2.chargedProgram, afterExpansion, suffix, body, Guest.guestFn_op_mcopy,
    OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar]

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem expansion_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64) (src dst len : U256Value.Words)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (srcLocal : source.locals.lookup (ofString "src") = some (U256Value.tuple src))
    (dstLocal : source.locals.lookup (ofString "dst") = some (U256Value.tuple dst))
    (lenLocal : source.locals.lookup (ofString "len") = some (U256Value.tuple len))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source program = (some (.returned returned), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost2.resultPair src len dst len current).2 + 50 ∧
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧
      MemoryExtend.View ready frame base (MemoryExtend.newLength current (MemoryExpansionCost2.resultPair src len dst len current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost2.resultPair src len dst len current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost2.resultPair src len dst len current).2) scratch ∧
      ready.locals.lookup (ofString "src") = some (U256Value.tuple src) ∧
      ready.locals.lookup (ofString "dst") = some (U256Value.tuple dst) ∧
      ready.locals.lookup (ofString "n") = some (.val (.word (SatWord.resultWord len))) ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + (chargeWord src dst len current).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost2.resultPair src len dst len current).2)).toNat ≤
        (wordAt ready.memory (frame + 184#64)).toNat ∧
      ChargeWithMemory.OutsideEffect source ready frame base scratch ∧
      (U256Zero.resultWord len = 0#64 →
        (SatWord.resultWord src).toNat + (SatWord.resultWord len).toNat ≤ (MemoryExtend.newLength current (MemoryExpansionCost2.resultPair src len dst len current).2).toNat ∧
        (SatWord.resultWord dst).toNat + (SatWord.resultWord len).toNat ≤ (MemoryExtend.newLength current (MemoryExpansionCost2.resultPair src len dst len current).2).toNat) ∧
      (∀ key, key ≠ ofString "frame_mem_ptr" → ready.globals.lookup key = source.globals.lookup key) ∧
      ready.memaddrs = source.memaddrs ∧
      evaluateHOLFiniteState ready afterExpansion = (some (.returned returned), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  have costView : MemoryExpansionCost.View source frame current := ⟨view.installed, view.ev, view.mapped 32 (by simp), view.lengthCell⟩
  obtain ⟨setupPaid, checkpoint, inner, setupBound, setupFits, setupFields, setupClock, srcCell, dstCell, nCell, xCell, costCell, run, scopeFields, scopeClock⟩ :=
    setup_value source post frame current src dst len costView srcLocal dstLocal lenLocal returned normal
  have memory := Input.LocalEffects.memory_of_erase source checkpoint setupFields
  have checkpointView := view.after_erase setupFields
  have checkpointCap : regularBudget checkpoint.memory frame ≤ 16777216 := by rw [memory]; exact cap
  have checkpointCovered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt checkpoint.memory (frame + 184#64)).toNat := by rw [memory]; exact covered
  have args : evalListHOLFinite checkpoint (h := fun address => Classical.propDecidable (checkpoint.memaddrs address)) [localVar "cost"] = some [.val (.word (chargeWord src dst len current))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, costCell]
  have covers : (MemoryExpansionCost2.resultPair src len dst len current).1.toNat ≤ (chargeWord src dst len current).toNat := by
    rw [chargeWord, SaturatingAdd.result_nat]
    have bound := (MemoryExpansionCost2.resultPair src len dst len current).1.isLt
    omega
  rw [afterFee_shape] at run
  obtain ⟨ready, tailFits, tailClock, locals, readyView, budget, credit, nextCovered, away, firstRange, secondRange, globals, domain, tailRun⟩ :=
    MemoryExpansionCost2.charged_normal checkpoint inner frame base current capacity pointer scratch (chargeWord src dst len current) src len dst len
      checkpointView xCell checkpointCap checkpointCovered covers [localVar "cost"] args afterExpansion returned run
  let tailPaid := MemoryExtend.price current capacity (MemoryExpansionCost2.resultPair src len dst len current).2 + 2
  refine ⟨setupPaid + tailPaid, ready, inner, by dsimp only [tailPaid]; omega, ?_, ?_, readyView,
    by rw [locals]; exact srcCell, by rw [locals]; exact dstCell, by rw [locals]; exact nCell, ?_, ?_, nextCovered, ?_,
    fun nonempty => ⟨firstRange nonempty, secondRange nonempty⟩, ?_, ?_, tailRun, scopeFields, scopeClock⟩
  · rw [setupClock] at tailFits
    dsimp only [tailPaid]
    omega
  · rw [tailClock, setupClock]
    dsimp only [tailPaid]
    omega
  · rw [budget, memory]
  · rw [credit, memory]
  · intro query outside notLength notCapacity notGas notUsed
    rw [away query outside notLength notCapacity notGas notUsed, memory]
  · intro key different
    rw [globals key different]
    have preserved := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals.lookup key) setupFields
    exact preserved
  · rw [domain]
    have preserved := congrArg PanSemStateFiniteExact.memaddrs setupFields
    exact preserved

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.afterFee_shape
#print axioms InitECandidate.Solver.GasBudget.Mcopy.expansion_prefix
