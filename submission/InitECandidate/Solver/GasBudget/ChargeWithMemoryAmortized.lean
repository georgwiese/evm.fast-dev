import InitECandidate.Solver.GasBudget.ChargeWithMemoryCall
import InitECandidate.Solver.GasBudget.MemoryExtendAmortized

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix Input.RlpWrite

theorem call_potential (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch fee : BitVec 64) (start size : U256Value.Words) (arguments : List (ExpHOL 64))
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word fee), U256Value.tuple start, U256Value.tuple size])
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_with_memory") arguments) = (none, post)) :
    ∃ paid : Nat, paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      paid + MemoryExtend.potential current capacity ≤
        MemoryExtend.potential (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)
          (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2) + 28 := by
  obtain ⟨paid, bound, funded, clock, postView, budget, credit, memoryCost, away⟩ :=
    call_normal source post frame base current capacity pointer scratch fee start size arguments view argsRead cap covered normal
  let amount := SaturatingAdd.resultWord fee (MemoryExpansionCost.resultPair start size current).1
  let used := (wordAt source.memory (frame + 184#64)).toNat
  have beforeUsed : used ≤ 16777216 := by
    dsimp only [used]
    unfold regularBudget at cap
    omega
  have afterUsed : (wordAt post.memory (frame + 184#64)).toNat ≤ 16777216 := by
    have capped : regularBudget post.memory frame ≤ 16777216 := by rw [budget]; exact cap
    unfold regularBudget at capped
    omega
  have amountFits : amount.toNat ≤ 16777216 - used := by
    change (wordAt post.memory (frame + 184#64)).toNat = used + amount.toNat at credit
    omega
  have covers : (MemoryExpansionCost.resultPair start size current).1.toNat ≤ amount.toNat := by
    dsimp only [amount]
    rw [SaturatingAdd.result_nat]
    have small := (MemoryExpansionCost.resultPair start size current).1.isLt
    omega
  have advance := MemoryExpansionCost.affordable start size current amount used (16777216 - used) view.lengthAligned covered
    (by omega) amountFits covers
  have cost := MemoryExtend.price_potential source frame base current capacity pointer scratch (MemoryExpansionCost.resultPair start size current).2 amount used view advance
  exact ⟨paid, funded, clock, by omega⟩

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.call_potential
