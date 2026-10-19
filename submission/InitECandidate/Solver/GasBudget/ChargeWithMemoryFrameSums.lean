import InitECandidate.Solver.GasBudget.ChargeWithMemoryCall

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix Input.RlpWrite

theorem call_sums (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch fee : BitVec 64) (start size : U256Value.Words) (arguments : List (ExpHOL 64))
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word fee), U256Value.tuple start, U256Value.tuple size])
    (cap : regularBudget source.memory frame ≤ 16777216)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (ancestors : List (BitVec 64))
    (owned : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat), Arenas.Outside base scratch (ancestor + BitVec.ofNat 64 offset))
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      ancestor + BitVec.ofNat 64 offset ≠ frame + 32#64 ∧ ancestor + BitVec.ofNat 64 offset ≠ frame + 40#64 ∧
      ancestor + BitVec.ofNat 64 offset ≠ frame + 64#64 ∧ ancestor + BitVec.ofNat 64 offset ≠ frame + 184#64)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_with_memory") arguments) = (none, post)) :
    ∃ paid : Nat, paid ≤ MemoryExtend.price current capacity (MemoryExpansionCost.resultPair start size current).2 + 25 ∧ paid ≤ source.clock ∧
      post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)
        (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2)
        (base + MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start size current).2) scratch ∧
      FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) ∧
      FrameSums.used post.memory (frame :: ancestors) = FrameSums.used source.memory (frame :: ancestors) +
        (SaturatingAdd.resultWord fee (MemoryExpansionCost.resultPair start size current).1).toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start size current).2)).toNat ≤
        (wordAt post.memory (frame + 184#64)).toNat := by
  obtain ⟨paid, bound, funded, clock, postView, budget, credit, memoryCost, away⟩ :=
    call_normal source post frame base current capacity pointer scratch fee start size arguments view argsRead cap covered normal
  have cells : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      post.memory (ancestor + BitVec.ofNat 64 offset) = source.memory (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    obtain ⟨notLength, notCapacity, notGas, notUsed⟩ := apart ancestor member offset inside
    exact away _ (owned ancestor member offset inside) notLength notCapacity notGas notUsed
  have ancestorBudget := FrameSums.budget_congr source.memory post.memory ancestors cells
  have ancestorUsed := FrameSums.used_congr source.memory post.memory ancestors (by intro ancestor member; exact cells ancestor member 184 (by simp))
  refine ⟨paid, bound, funded, clock, postView, ?_, ?_, memoryCost⟩
  · change regularBudget post.memory frame + FrameSums.budget post.memory ancestors = regularBudget source.memory frame + FrameSums.budget source.memory ancestors
    rw [budget, ancestorBudget]
  · change (wordAt post.memory (frame + 184#64)).toNat + FrameSums.used post.memory ancestors =
      ((wordAt source.memory (frame + 184#64)).toNat + FrameSums.used source.memory ancestors) + _
    rw [credit, ancestorUsed]
    omega

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.call_sums
