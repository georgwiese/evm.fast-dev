import InitECandidate.Solver.GasBudget.MemoryExtendTail

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem tail_view (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat)
    (view : View source frame base length capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance length expand amount used)
    (postEq : post = expandedState source frame base length capacity pointer expand)
    (lengthCell : post.memory (frame + 32#64) = .word (newLength length expand))
    (capacityCell : post.memory (frame + 40#64) = .word (nextCapacity length capacity expand))
    (region : Geometry base length capacity pointer scratch expand)
    (away : ∀ query, Arenas.Outside base scratch query → query ≠ frame + 32#64 → query ≠ frame + 40#64 → post.memory query = source.memory query) :
    View post frame base (newLength length expand) (nextCapacity length capacity expand)
      (base + nextCapacity length capacity expand) scratch := by
  have code : post.code = source.code := by
    rw [postEq]; unfold expandedState capacityState; split <;> rfl
  have mapped : post.memaddrs = source.memaddrs := by
    rw [postEq]; unfold expandedState capacityState; split <;> rfl
  have globals : post.globals = (capacityState source frame base length capacity pointer expand).globals := by rw [postEq]; rfl
  have ev : post.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    rw [globals]
    unfold capacityState
    split
    · simpa [growthState, Arenas.post, Arenas.pointerName, HolFiniteMapExact.update, FUPDATE, ofString] using view.ev
    · exact view.ev
  have scratchGlobal : post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    rw [globals]
    unfold capacityState
    split
    · simpa [growthState, Arenas.post, Arenas.pointerName, HolFiniteMapExact.update, FUPDATE, ofString] using view.scratchGlobal
    · exact view.scratchGlobal
  have pointerGlobal : post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word (base + nextCapacity length capacity expand))) := by
    rw [globals]
    unfold capacityState
    split
    · simp [growthState, Arenas.post, Arenas.pointerName, HolFiniteMapExact.update, FUPDATE, region.newPointer]
    · rename_i noGrow
      have same : nextCapacity length capacity expand = capacity := by simp [nextCapacity, noGrow]
      rw [same, ← region.oldPointer]
      exact view.pointerGlobal
  have fits : base.toNat + (nextCapacity length capacity expand).toNat < 2 ^ 64 := by
    have bound := scratch.isLt
    have extent := region.extent
    omega
  have cursor := BitVec.toNat_add_of_lt fits
  refine ⟨?_, ev, ?_, ?_, lengthCell, capacityCell, region.nextContains, region.nextSlack,
    advance.aligned, region.nextAligned, view.baseAligned, pointerGlobal, scratchGlobal, cursor, ?_, view.scratchAligned,
    view.frameAbove, view.frameFits, ?_⟩
  · rw [code]; exact view.installed
  · intro offset inside; rw [mapped]; exact view.mapped offset inside
  · rw [away _ (view.header_outside 24 (by decide)) (offsets_ne frame 24#64 32#64 (by decide)) (offsets_ne frame 24#64 40#64 (by decide))]
    exact view.baseCell
  · apply BitVec.le_def.mpr
    rw [cursor]
    exact region.extent
  · intro query low high aligned
    rw [mapped]
    exact view.arena query low high aligned

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.tail_view
