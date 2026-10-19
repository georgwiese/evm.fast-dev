import InitECandidate.Solver.GasBudget.MemoryExtendGrowBranch

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def growthPrice (length capacity expand : BitVec 64) : Nat :=
  if capacity < newLength length expand then (nextCapacity length capacity expand - capacity).toNat / 32 + 2 else 0

def capacityState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer expand : BitVec 64) :=
  if capacity < newLength length expand then growthState source frame base length capacity pointer expand else source

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem growth_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat)
    (view : View source frame base length capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance length expand amount used)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (nlenLocal : source.locals.lookup (ofString "nlen") = some (.val (.word (newLength length expand))))
    (normal : evaluateHOLFiniteState source growthGuard = (none, post)) :
    growthPrice length capacity expand ≤ source.clock ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase (capacityState source frame base length capacity pointer expand) ∧
      post.clock = source.clock - growthPrice length capacity expand ∧
      Geometry base length capacity pointer scratch expand ∧
      ClearView post frame base scratch ∧
      post.memory (frame + 40#64) = .word (nextCapacity length capacity expand) ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 40#64 → post.memory query = source.memory query) := by
  by_cases grow : capacity < newLength length expand
  · have branch : evaluateHOLFiniteState source growthGuard = evaluateHOLFiniteState source growBranch := by
      simp [growthGuard, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, capLocal, nlenLocal,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, grow]
    rw [branch] at normal
    simpa only [growthPrice, capacityState, if_pos grow] using
      grow_branch_normal source post frame base length capacity pointer scratch expand amount used view advance grow capLocal nlenLocal normal
  · have branch : evaluateHOLFiniteState source growthGuard = (none, source) := by
      simp [growthGuard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar, capLocal, nlenLocal,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, grow]
    rw [branch] at normal
    have postEq : post = source := (congrArg Prod.snd normal).symm
    rw [postEq]
    have same : nextCapacity length capacity expand = capacity := by simp [nextCapacity, grow]
    have room : Arenas.Room .up pointer scratch (nextCapacity length capacity expand - capacity) := by
      rw [same, BitVec.sub_self]
      change pointer.toNat + (0#64).toNat ≤ scratch.toNat
      simpa using (BitVec.le_def.mp view.ordered)
    have region := geometry source frame base length capacity pointer scratch expand amount view used advance room
    refine ⟨by simp [growthPrice, grow], by simp [capacityState, grow], by simp [growthPrice, grow], region,
      ⟨view.installed, view.ev, view.mapped 24 (by simp), view.mapped 32 (by simp), view.baseCell, view.arena⟩, ?_, ?_⟩
    · rw [same]; exact view.capacityCell
    · intro query _ _; rfl

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.growth_guard_normal
