import InitECandidate.Solver.GasBudget.RunFramesMemoryTerminal
import InitECandidate.Solver.GasBudget.RunFramesTerminalRank

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The real expanded buffer may change, but owned ancestor ledgers cannot.
Thus even a zero-charge terminal opcode decreases the physical frame rank. -/
theorem MemoryTerminal.rank {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont base scratch oldLength oldCapacity length capacity pointer : BitVec 64} {ceiling : Nat}
    (terminal : MemoryTerminal source post frame cont base scratch oldLength oldCapacity length capacity pointer ceiling)
    (ancestors : List (BitVec 64)) (limit : Nat)
    (owned : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      Arenas.Outside base scratch (ancestor + BitVec.ofNat 64 offset))
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      (∀ field ∈ revertWriteOffsets, ancestor + BitVec.ofNat 64 offset ≠ frame + BitVec.ofNat 64 field) ∧
      ancestor + BitVec.ofNat 64 offset ≠ cont + 32#64)
    (cap : FrameSums.budget source.memory (frame :: ancestors) ≤ limit) :
    FrameRank.value limit post.memory (frame :: ancestors) false < FrameRank.value limit source.memory (frame :: ancestors) true ∧
      ImmediateDone post frame cont ∧
      FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) := by
  obtain ⟨paid, funded, clock, view, budget, used, cost, marked, mapped, continuation, amortized, outside⟩ := terminal
  have cells : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      post.memory (ancestor + BitVec.ofNat 64 offset) = source.memory (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    exact outside _ (owned ancestor member offset inside) (apart ancestor member offset inside).1 (apart ancestor member offset inside).2
  have ancestorBudget := FrameSums.budget_congr source.memory post.memory ancestors cells
  have ancestorUsed := FrameSums.used_congr source.memory post.memory ancestors (by intro ancestor member; exact cells ancestor member 184 (by simp))
  have liveBudget : FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) := by
    change regularBudget post.memory frame + FrameSums.budget post.memory ancestors = regularBudget source.memory frame + FrameSums.budget source.memory ancestors
    rw [budget, ancestorBudget]
  have liveUsed : FrameSums.used source.memory (frame :: ancestors) ≤ FrameSums.used post.memory (frame :: ancestors) := by
    change (wordAt source.memory (frame + 184#64)).toNat + FrameSums.used source.memory ancestors ≤
      (wordAt post.memory (frame + 184#64)).toNat + FrameSums.used post.memory ancestors
    rw [ancestorUsed]
    exact Nat.add_le_add_right used _
  have bounded : FrameSums.used post.memory (frame :: ancestors) ≤ limit :=
    (FrameSums.used_le_budget post.memory _).trans (by rw [liveBudget]; exact cap)
  exact ⟨FrameRank.terminal limit source.memory post.memory _ _ (by simp) liveUsed bounded rfl,
    .marked 1#64 mapped marked (by decide), liveBudget⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.MemoryTerminal.rank
