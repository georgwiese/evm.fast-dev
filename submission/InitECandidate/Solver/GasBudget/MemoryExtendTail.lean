import InitECandidate.Solver.GasBudget.MemoryExtendGuard

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

theorem growth_guard_prefix (key : MlS) (other : key ≠ ofString "ncap") : Input.LocalPrefix key growthGuard := by
  exact .ite _ (.dec _ _ _ other (.seq (.ite _ (.assign _ _ other) .skip)
    (.seq (.call none _ _ (by simp)) (.seq (.call none _ _ (by simp)) (.store _ _))))) .skip

def bodyPrice (length capacity expand : BitVec 64) : Nat :=
  growthPrice length capacity expand + expand.toNat / 32 + 1

def expandedState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer expand : BitVec 64) :=
  emptyLocalsHOLFinite {capacityState source frame base length capacity pointer expand with
    memory := StoreWord.put
      (Zero.finalMemory (capacityState source frame base length capacity pointer expand).memory (base + length) expand.toNat)
      (frame + 32#64) (newLength length expand)
    clock := source.clock - bodyPrice length capacity expand}

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem tail_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat) (returned : ValueHOL 64)
    (view : View source frame base length capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance length expand amount used)
    (lengthLocal : source.locals.lookup (ofString "len") = some (.val (.word length)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (expandLocal : source.locals.lookup (ofString "expand_by") = some (.val (.word expand)))
    (nlenLocal : source.locals.lookup (ofString "nlen") = some (.val (.word (newLength length expand))))
    (normal : evaluateHOLFiniteState source afterNewLength = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ bodyPrice length capacity expand ≤ source.clock ∧
      post = expandedState source frame base length capacity pointer expand ∧
      post.memory (frame + 32#64) = .word (newLength length expand) ∧
      post.memory (frame + 40#64) = .word (nextCapacity length capacity expand) ∧
      Geometry base length capacity pointer scratch expand ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 32#64 → query ≠ frame + 40#64 → post.memory query = source.memory query) := by
  obtain ⟨middle, guardRun, finalRun, retained⟩ := (growth_guard_prefix (ofString "nlen") (by decide)).normal_continue source post afterGrowth returned normal
  obtain ⟨growthFits, fields, clock, region, clearView, capacityCell, growthAway⟩ :=
    growth_guard_normal source middle frame base length capacity pointer scratch expand amount used view advance capLocal nlenLocal guardRun
  have keep (key : MlS) (other : key ≠ ofString "ncap") : middle.locals.lookup key = source.locals.lookup key := by
    have saved := ((growth_guard_prefix key other).summary source).1
    rw [guardRun] at saved
    exact saved rfl
  have middleLength := (keep (ofString "len") (by decide)).trans lengthLocal
  have middleExpand := (keep (ofString "expand_by") (by decide)).trans expandLocal
  have middleNext := retained.trans nlenLocal
  have lower : base.toNat ≤ (base + length).toNat := by rw [region.clearNumber]; omega
  have small : expand.toNat + 32 < 2 ^ 64 := by
    have natural := advance.natural
    have bound := advance.byteBound
    omega
  obtain ⟨value, finalFits, finalEq, lengthCell, finalAway⟩ :=
    final_clear_normal middle post frame base scratch length expand returned clearView middleLength middleExpand middleNext lower
      region.clearExtent region.clearAligned region.expandAligned small finalRun
  have funded : bodyPrice length capacity expand ≤ source.clock := by
    rw [clock] at finalFits
    unfold bodyPrice
    omega
  have spent : middle.clock - (expand.toNat / 32 + 1) = source.clock - bodyPrice length capacity expand := by
    rw [clock]
    unfold bodyPrice
    omega
  have exactPost : post = expandedState source frame base length capacity pointer expand := by
    rw [finalEq]
    change emptyLocalsHOLFinite {middle with memory := _, clock := middle.clock - (expand.toNat / 32 + 1)} = _
    rw [spent]
    have transported := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => emptyLocalsHOLFinite {state with
      memory := StoreWord.put (Zero.finalMemory state.memory (base + length) expand.toNat) (frame + 32#64) (newLength length expand)
      clock := source.clock - bodyPrice length capacity expand}) fields
    exact transported
  have away : ∀ query, Arenas.Outside base scratch query → query ≠ frame + 32#64 → query ≠ frame + 40#64 → post.memory query = source.memory query := by
    intro query outside notLength notCapacity
    exact (finalAway query outside notLength).trans (growthAway query outside notCapacity)
  have finalCapacity : post.memory (frame + 40#64) = .word (nextCapacity length capacity expand) := by
    rw [finalAway _ (view.header_outside 40 (by decide)) (offsets_ne frame 40#64 32#64 (by decide))]
    exact capacityCell
  exact ⟨value, funded, exactPost, lengthCell, finalCapacity, region, away⟩

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.growth_guard_prefix
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.tail_normal
