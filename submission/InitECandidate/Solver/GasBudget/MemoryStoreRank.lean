import InitECandidate.Solver.GasBudget.DispatchMemoryStore
import InitECandidate.Solver.GasBudget.MemoryExtendAmortized

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input.RlpWrite

theorem store_rank (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64) (arguments : List (ExpHOL 64))
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (covered : (MemoryGasCost.resultWord current).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat)
    (ancestors : List (BitVec 64)) (limit : Nat) (limitBound : limit ≤ 16777216)
    (cap : FrameSums.budget source.memory (frame :: ancestors) ≤ limit)
    (owned : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat), Arenas.Outside base scratch (ancestor + BitVec.ofNat 64 offset))
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      ancestor + BitVec.ofNat 64 offset ≠ frame + 0#64 ∧ ancestor + BitVec.ofNat 64 offset ≠ frame + 16#64 ∧
      ancestor + BitVec.ofNat 64 offset ≠ frame + 32#64 ∧ ancestor + BitVec.ofNat 64 offset ≠ frame + 40#64 ∧
      ancestor + BitVec.ofNat 64 offset ≠ frame + 64#64 ∧ ancestor + BitVec.ofNat 64 offset ≠ frame + 184#64)
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word 82#64)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, post)) :
    ∃ (start : U256Value.Words) (paid : Nat), paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) ∧
      FrameSums.used source.memory (frame :: ancestors) + 3 ≤ FrameSums.used post.memory (frame :: ancestors) ∧
      (∀ nextActive, FrameRank.value limit post.memory (frame :: ancestors) nextActive < FrameRank.value limit source.memory (frame :: ancestors) true) ∧
      paid + MemoryExtend.potential current capacity ≤
        MemoryExtend.potential (MemoryExtend.newLength current (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2)
          (MemoryExtend.nextCapacity current capacity (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2) + 47 := by
  have parentCap : regularBudget source.memory frame ≤ 16777216 := by
    change regularBudget source.memory frame + FrameSums.budget source.memory ancestors ≤ limit at cap
    omega
  obtain ⟨start, paid, bound, funded, clock, postView, budget, credit, memoryCost, depth, away⟩ :=
    store_call_normal source post frame base current capacity pointer scratch arguments view parentCap covered argsRead normal
  let amount := SaturatingAdd.resultWord 3#64 (MemoryExpansionCost.resultPair start MemoryStore.size32 current).1
  change (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + amount.toNat at credit
  have cells : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      post.memory (ancestor + BitVec.ofNat 64 offset) = source.memory (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    obtain ⟨notPC, notSP, notLength, notCapacity, notGas, notUsed⟩ := apart ancestor member offset inside
    exact away _ (owned ancestor member offset inside) notPC notSP notLength notCapacity notGas notUsed
  have ancestorBudget := FrameSums.budget_congr source.memory post.memory ancestors cells
  have ancestorUsed := FrameSums.used_congr source.memory post.memory ancestors (by intro ancestor member; exact cells ancestor member 184 (by simp))
  have liveBudget : FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) := by
    change regularBudget post.memory frame + FrameSums.budget post.memory ancestors = regularBudget source.memory frame + FrameSums.budget source.memory ancestors
    rw [budget, ancestorBudget]
  have liveCredit : FrameSums.used post.memory (frame :: ancestors) = FrameSums.used source.memory (frame :: ancestors) + amount.toNat := by
    change (wordAt post.memory (frame + 184#64)).toNat + FrameSums.used post.memory ancestors =
      ((wordAt source.memory (frame + 184#64)).toNat + FrameSums.used source.memory ancestors) + amount.toNat
    rw [credit, ancestorUsed]
    omega
  have positive : 3 ≤ amount.toNat := BitVec.le_def.mp (SaturatingAdd.ge_left 3#64 _)
  have usedCap : FrameSums.used post.memory (frame :: ancestors) ≤ limit :=
    (FrameSums.used_le_budget post.memory _).trans (by rw [liveBudget]; exact cap)
  have progression : FrameSums.used source.memory (frame :: ancestors) + 3 ≤ FrameSums.used post.memory (frame :: ancestors) := by rw [liveCredit]; omega
  let used := (wordAt source.memory (frame + 184#64)).toNat
  have parentAfter : (wordAt post.memory (frame + 184#64)).toNat ≤ limit := by
    change (wordAt post.memory (frame + 184#64)).toNat + FrameSums.used post.memory ancestors ≤ limit at usedCap
    omega
  have amountFits : amount.toNat ≤ limit - used := by
    change (wordAt post.memory (frame + 184#64)).toNat = used + amount.toNat at credit
    omega
  have oldBound : used ≤ limit := by change (wordAt post.memory (frame + 184#64)).toNat = used + amount.toNat at credit; omega
  have covers : (MemoryExpansionCost.resultPair start MemoryStore.size32 current).1.toNat ≤ amount.toNat := by
    dsimp only [amount]
    rw [SaturatingAdd.result_nat]
    have small := (MemoryExpansionCost.resultPair start MemoryStore.size32 current).1.isLt
    omega
  have advance := MemoryExpansionCost.affordable start MemoryStore.size32 current amount used (limit - used) view.lengthAligned covered (by omega) amountFits covers
  have amortized := MemoryExtend.price_potential source frame base current capacity pointer scratch (MemoryExpansionCost.resultPair start MemoryStore.size32 current).2 amount used view advance
  refine ⟨start, paid, funded, clock, liveBudget, progression, ?_, by omega⟩
  intro nextActive
  exact FrameRank.charged limit source.memory post.memory (frame :: ancestors) (frame :: ancestors) nextActive (by simp) (by omega) usedCap (by simp)

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.store_rank
