import InitECandidate.Solver.GasBudget.RunFramesTerminalFrame

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- All actual pre-charge terminal classifications carry sufficient physical
memory information for the live-frame rank. Ownership is a current-state
separation obligation; no handler execution or future sum is assumed. -/
theorem TerminalPrefix.rank {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont : BitVec 64} {ceiling : Nat}
    (terminal : TerminalPrefix source post frame cont ceiling) (ancestors : List (BitVec 64)) (limit : Nat)
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      ancestor + BitVec.ofNat 64 offset ≠ frame + 16#64 ∧
      (∀ field ∈ FrameException.writeOffsets, ancestor + BitVec.ofNat 64 offset ≠ frame + BitVec.ofNat 64 field) ∧
      ancestor + BitVec.ofNat 64 offset ≠ cont + 32#64)
    (cap : FrameSums.budget source.memory (frame :: ancestors) ≤ limit) :
    FrameRank.value limit post.memory (frame :: ancestors) false < FrameRank.value limit source.memory (frame :: ancestors) true ∧
      ImmediateDone post frame cont ∧
      FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) := by
  have done := terminal.immediate_done
  obtain ⟨paid, bound, fits, clock, fields, parentBudget, marked, mapped, continuation, memoryEffect⟩ := terminal
  obtain ⟨budget, used⟩ := memoryEffect.sums ancestors apart parentBudget
  have bounded : FrameSums.used post.memory (frame :: ancestors) ≤ limit := by
    apply (FrameSums.used_le_budget post.memory (frame :: ancestors)).trans
    rw [budget]
    exact cap
  exact ⟨FrameRank.terminal limit source.memory post.memory _ _ (by simp) used bounded rfl, done, budget⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.TerminalPrefix.rank
