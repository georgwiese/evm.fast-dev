import InitECandidate.Solver.GasBudget.ChargeWithMemoryCall
import InitECandidate.Solver.GasBudget.MemoryExpansionCostRange

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input.RlpWrite

theorem call_range (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch fee : BitVec 64) (start size : U256Value.Words) (arguments : List (ExpHOL 64))
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word fee), U256Value.tuple start, U256Value.tuple size])
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (nonempty : U256Zero.resultWord size = 0#64)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_with_memory") arguments) = (none, post)) :
    (SatWord.resultWord start).toNat + (SatWord.resultWord size).toNat ≤
      (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2).toNat := by
  obtain ⟨paid, bound, funded, clock, postView, budget, credit, memoryCost, away⟩ :=
    call_normal source post frame base current capacity pointer scratch fee start size arguments view argsRead cap covered normal
  let amount := SaturatingAdd.resultWord fee (MemoryExpansionCost.resultPair start size current).1
  have afterUsed : (wordAt post.memory (frame + 184#64)).toNat ≤ 16777216 := by
    have capped : regularBudget post.memory frame ≤ 16777216 := by rw [budget]; exact cap
    unfold regularBudget at capped
    omega
  have amountSmall : amount.toNat ≤ 16777216 := by
    change (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + amount.toNat at credit
    omega
  have covers : (MemoryExpansionCost.resultPair start size current).1.toNat ≤ amount.toNat := by
    dsimp only [amount]
    rw [SaturatingAdd.result_nat]
    have small := (MemoryExpansionCost.resultPair start size current).1.isLt
    omega
  exact MemoryExpansionCost.range_of_affordable start size current amount view.lengthAligned nonempty amountSmall covers

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.call_range
