import InitECandidate.Solver.GasBudget.RunFramesFrameTerminal
import InitECandidate.Solver.GasBudget.MemoryBufferHandlerView

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem FrameTerminal.rank {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont : BitVec 64} {ceiling : Nat}
    (terminal : FrameTerminal source post frame cont ceiling) (ancestors : List (BitVec 64)) (limit : Nat)
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      ancestor + BitVec.ofNat 64 offset ≠ frame + 16#64 ∧
      MemoryWriter.BytesAway (frame + 240#64) (ancestor + BitVec.ofNat 64 offset) 20 ∧
      (∀ field ∈ FrameException.writeOffsets, ancestor + BitVec.ofNat 64 offset ≠ frame + BitVec.ofNat 64 field) ∧
      ancestor + BitVec.ofNat 64 offset ≠ cont + 32#64)
    (cap : FrameSums.budget source.memory (frame :: ancestors) ≤ limit) :
    FrameRank.value limit post.memory (frame :: ancestors) false < FrameRank.value limit source.memory (frame :: ancestors) true ∧
      ImmediateDone post frame cont ∧
      FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) := by
  obtain ⟨paid, bound, funded, clock, fields, parentBudget, ev, continuation, done⟩ := terminal.completion
  have cells : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      post.memory (ancestor + BitVec.ofNat 64 offset) = source.memory (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    obtain ⟨notSP, footerAway, notFrame, notCont⟩ := apart ancestor member offset inside
    exact terminal.memoryEffect.outside _ notSP footerAway notFrame notCont
  have ancestorBudget := FrameSums.budget_congr source.memory post.memory ancestors cells
  have ancestorUsed := FrameSums.used_congr source.memory post.memory ancestors (by intro ancestor member; exact cells ancestor member 184 (by simp))
  have budget : FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) := by
    change regularBudget post.memory frame + FrameSums.budget post.memory ancestors = regularBudget source.memory frame + FrameSums.budget source.memory ancestors
    rw [parentBudget, ancestorBudget]
  have used : FrameSums.used source.memory (frame :: ancestors) ≤ FrameSums.used post.memory (frame :: ancestors) := by
    change (wordAt source.memory (frame + 184#64)).toNat + FrameSums.used source.memory ancestors ≤
      (wordAt post.memory (frame + 184#64)).toNat + FrameSums.used post.memory ancestors
    rw [ancestorUsed]
    exact Nat.add_le_add_right terminal.memoryEffect.used _
  have bounded : FrameSums.used post.memory (frame :: ancestors) ≤ limit :=
    (FrameSums.used_le_budget post.memory _).trans (by rw [budget]; exact cap)
  exact ⟨FrameRank.terminal limit source.memory post.memory _ _ (by simp) used bounded rfl, done, budget⟩

theorem FrameTerminal.buffer_view {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont base length capacity pointer scratch : BitVec 64} {ceiling : Nat}
    (terminal : FrameTerminal source post frame cont ceiling)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (aligned : frame.toNat % 8 = 0)
    (apart : ∀ offset ∈ ([24, 32, 40] : List Nat), frame + BitVec.ofNat 64 offset ≠ cont + 32#64) :
    MemoryExtend.View post frame base length capacity pointer scratch := by
  have header (offset : Nat) (member : offset ∈ ([24, 32, 40] : List Nat)) :
      post.memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset) := by
    apply terminal.memoryEffect.outside _ _ _ _ (apart offset member)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals exact offsets_ne frame _ _ (by decide)
    · apply AddressMasked.header_away frame offset aligned view.frameFits
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    · intro field inside
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals simp only [FrameException.writeOffsets, List.mem_cons, List.not_mem_nil, or_false] at inside
      all_goals rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact offsets_ne frame _ _ (by decide)
  have current := view.with_memory post.memory ((header 24 (by simp)).trans view.baseCell)
    ((header 32 (by simp)).trans view.lengthCell) ((header 40 (by simp)).trans view.capacityCell)
  obtain ⟨paid, bound, funded, clock, fields, budget, ev, continuation, done⟩ := terminal.completion
  exact current.after_erase (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) fields)

theorem FrameTerminal.memory_cost {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont length : BitVec 64} {ceiling : Nat}
    (terminal : FrameTerminal source post frame cont ceiling)
    (covered : (MemoryGasCost.resultWord length).toNat ≤ (wordAt source.memory (frame + 184#64)).toNat) :
    (MemoryGasCost.resultWord length).toNat ≤ (wordAt post.memory (frame + 184#64)).toNat :=
  covered.trans terminal.memoryEffect.used

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.FrameTerminal.rank
#print axioms InitECandidate.Solver.GasBudget.RunFrames.FrameTerminal.buffer_view
#print axioms InitECandidate.Solver.GasBudget.RunFrames.FrameTerminal.memory_cost
