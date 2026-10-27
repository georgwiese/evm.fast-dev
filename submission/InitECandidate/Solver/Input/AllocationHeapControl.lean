import InitECandidate.Solver.Input.NormalHeapEffects
import InitECandidate.Solver.PanControl
import InitECandidate.Solver.WitnessRadix.AllocationArithmetic

namespace InitECandidate.Solver.Input.NormalHeapEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual end of a returned array is also a lower bound for the next
allocation, so later list calls cannot overwrite the earlier record array. -/
theorem allocation_extent (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array amount : BitVec 64) (empty : Prop) [Decidable empty]
    (cell : source.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (high : array.toNat ≤ 2952790016) (aligned : array.toNat % 8 = 0)
    (absentAmount : empty → amount = 0#64)
    (room : ¬empty → array.toNat + amount.toNat ≤ 2952790016)
    (control : WitnessRadix.BackingLayout.control target = WitnessRadix.BackingLayout.control
      (if empty then source else WitnessRadix.PersistentAlloc.post source array amount)) :
    AtLeast (array.toNat + amount.toNat) target := by
  have globals := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control
  by_cases absent : empty
  · simp only [if_pos absent] at globals
    rw [absentAmount absent]
    exact ⟨array, (congrArg (fun table => table.lookup (ofString "heap_ptr")) globals).trans cell,
      by simp, high, aligned⟩
  · have guards := WitnessRadix.PersistentAlloc.guards array amount (room absent)
    refine ⟨WitnessRadix.PersistentAlloc.rounded array amount, ?_, guards.2.2.1, guards.2.2.2.1, guards.2.2.2.2⟩
    simp only [if_neg absent] at globals
    rw [show target.globals = (WitnessRadix.PersistentAlloc.post source array amount).globals from globals]
    simp [WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE]

theorem AtLeast.maximum {source : PanSemStateFiniteExact 64 Guest.HostMemory} {first second : Nat}
    (left : AtLeast first source) (right : AtLeast second source) : AtLeast (max first second) source := by
  obtain ⟨cursor, cell, low, high, aligned⟩ := left
  obtain ⟨other, otherCell, otherLow, _, _⟩ := right
  have same : other = cursor := by
    have equal := Option.some.inj (otherCell.symm.trans cell)
    cases equal
    rfl
  subst other
  exact ⟨cursor, cell, by omega, high, aligned⟩

end InitECandidate.Solver.Input.NormalHeapEffects


#print axioms InitECandidate.Solver.Input.NormalHeapEffects.allocation_extent
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.AtLeast.maximum
