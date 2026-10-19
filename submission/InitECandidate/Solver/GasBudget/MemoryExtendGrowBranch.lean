import InitECandidate.Solver.GasBudget.MemoryExtendClamp
import InitECandidate.Solver.GasBudget.MemoryExtendFinalClear

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def growthState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer expand : BitVec 64) :=
  {Arenas.post source .up pointer (nextCapacity length capacity expand - capacity) with
    memory := StoreWord.put (Zero.finalMemory source.memory (base + capacity) (nextCapacity length capacity expand - capacity).toNat)
      (frame + 40#64) (nextCapacity length capacity expand)
    clock := source.clock - ((nextCapacity length capacity expand - capacity).toNat / 32 + 2)}

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem grow_branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat)
    (view : View source frame base length capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance length expand amount used)
    (grow : capacity < newLength length expand)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (nlenLocal : source.locals.lookup (ofString "nlen") = some (.val (.word (newLength length expand))))
    (normal : evaluateHOLFiniteState source growBranch = (none, post)) :
    (nextCapacity length capacity expand - capacity).toNat / 32 + 2 ≤ source.clock ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase (growthState source frame base length capacity pointer expand) ∧
      post.clock = source.clock - ((nextCapacity length capacity expand - capacity).toNat / 32 + 2) ∧
      Geometry base length capacity pointer scratch expand ∧
      ClearView post frame base scratch ∧
      post.memory (frame + 40#64) = .word (nextCapacity length capacity expand) ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 40#64 → post.memory query = source.memory query) := by
  obtain ⟨inner, tailRun, postEq⟩ := grow_prefix_normal source post length capacity expand capLocal nlenLocal normal
  let entered := clamped (WitnessRadix.QueryBranch.bind source "ncap" (capacity * 2#64)) length capacity expand
  have fields : Input.LocalEffects.erase entered = Input.LocalEffects.erase source := by
    unfold entered clamped
    split <;> rfl
  have enteredView := view.after_erase fields
  have enteredCap : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    exact (clamped_other _ length capacity expand "cap" (by decide)).trans
      ((bind_lookup_other source "ncap" "cap" _ (by decide)).trans capLocal)
  have enteredNCap : entered.locals.lookup (ofString "ncap") = some (.val (.word (nextCapacity length capacity expand))) := by
    rw [nextCapacity, if_pos grow]
    exact clamped_value _ length capacity expand (bind_lookup_same _ _ _)
  obtain ⟨funded, innerEq, region, capCell, away⟩ := grow_tail_normal entered inner frame base length capacity pointer scratch expand amount used enteredView advance enteredCap enteredNCap tailRun
  have clock : entered.clock = source.clock := by unfold entered clamped; split <;> rfl
  rw [clock] at funded
  have finalFields : Input.LocalEffects.erase post = Input.LocalEffects.erase (growthState source frame base length capacity pointer expand) := by
    rw [postEq, innerEq]
    unfold entered clamped
    split <;> rfl
  have memory : post.memory = inner.memory := by rw [postEq]; rfl
  have queryAway : ∀ query, Arenas.Outside base scratch query → query ≠ frame + 40#64 → post.memory query = source.memory query := by
    intro query outside other
    rw [memory, away query outside other]
    unfold entered clamped
    split <;> rfl
  have newView : ClearView post frame base scratch := by
    have installed := congrArg PanSemStateFiniteExact.code finalFields
    have globals := congrArg PanSemStateFiniteExact.globals finalFields
    have mapped := congrArg PanSemStateFiniteExact.memaddrs finalFields
    change post.code = source.code at installed
    change post.globals = (Arenas.post source .up pointer (nextCapacity length capacity expand - capacity)).globals at globals
    change post.memaddrs = source.memaddrs at mapped
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [installed]; exact view.installed
    · rw [globals]
      simpa [growthState, Arenas.post, Arenas.pointerName, HolFiniteMapExact.update, FUPDATE, ofString] using view.ev
    · rw [mapped]; exact view.mapped 24 (by simp)
    · rw [mapped]; exact view.mapped 32 (by simp)
    · rw [queryAway _ (view.header_outside 24 (by decide)) (offsets_ne frame 24#64 40#64 (by decide))]
      exact view.baseCell
    · intro query low high aligned
      rw [mapped]
      exact view.arena query low high aligned
  have finalClock : post.clock = source.clock - ((nextCapacity length capacity expand - capacity).toNat / 32 + 2) := by
    rw [postEq, innerEq]
    change entered.clock - _ = source.clock - _
    rw [clock]
  exact ⟨funded, finalFields, finalClock, region, newView, by rw [memory]; exact capCell, queryAway⟩

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.grow_branch_normal
