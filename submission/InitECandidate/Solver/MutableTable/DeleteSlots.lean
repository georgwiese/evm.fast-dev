import InitECandidate.Solver.MutableTable.DeleteProgram
import InitECandidate.Solver.MutableTable.MemoryModel
import Mathlib.Data.List.Nodup

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- During the original backshift loop the deleted ordinal is ignored and
one physically used slot is the moving hole. Other ordinals remain dense. -/
def Covered {count : Nat} (entries : Fin count → Nat) (deleted : Fin count) (hole slot : Nat) : Prop :=
  slot = hole ∨ ∃ ordinal, ordinal ≠ deleted ∧ entries ordinal = slot

/-- Replacing one row by a fresh hole preserves distinct order entries. -/
theorem entries_update_injective {count : Nat} (entries : Fin count → Nat) (injective : Function.Injective entries)
    (ordinal : Fin count) (hole : Nat) (fresh : ∀ index, entries index ≠ hole) :
    Function.Injective (Function.update entries ordinal hole) := by
  classical
  intro first second same
  by_cases atFirst : first = ordinal
  · subst first
    by_cases atSecond : second = ordinal
    · exact atSecond.symm
    · have equal : hole = entries second := by simpa [Function.update, atSecond] using same
      exact (fresh second equal.symm).elim
  · by_cases atSecond : second = ordinal
    · subst second
      have equal : entries first = hole := by simpa [Function.update, atFirst] using same
      exact (fresh first equal).elim
    · apply injective
      simpa [Function.update, atFirst, atSecond] using same

/-- The old moved slot becomes fresh after its ordinal is replaced by the
old hole. This is independent of the hash-dependent movement decision. -/
theorem entries_update_fresh {count : Nat} (entries : Fin count → Nat) (injective : Function.Injective entries)
    (ordinal : Fin count) (hole slot : Nat) (stored : entries ordinal = slot) (different : hole ≠ slot) :
    ∀ index, Function.update entries ordinal hole index ≠ slot := by
  classical
  intro index equal
  by_cases same : index = ordinal
  · subst index
    exact different (by simpa [Function.update] using equal)
  · have original : entries index = entries ordinal := by simpa [Function.update, same, stored] using equal
    exact same (injective original)

/-- One backshift exchanges the moved slot and the hole without changing
which used bytes must be one. The removed ordinal stays excluded. -/
theorem covered_update {count : Nat} (entries : Fin count → Nat) (deleted moved : Fin count) (hole slot query : Nat)
    (active : moved ≠ deleted) (stored : entries moved = slot) :
    Covered (Function.update entries moved hole) deleted slot query ↔ Covered entries deleted hole query := by
  classical
  constructor
  · rintro (same | ⟨index, notDeleted, equal⟩)
    · exact Or.inr ⟨moved, active, stored.trans same.symm⟩
    · by_cases same : index = moved
      · subst index
        exact Or.inl (by simpa [Function.update] using equal.symm)
      · exact Or.inr ⟨index, notDeleted, by simpa [Function.update, same] using equal⟩
  · rintro (same | ⟨index, notDeleted, equal⟩)
    · exact Or.inr ⟨moved, active, by simpa [Function.update] using same.symm⟩
    · by_cases same : index = moved
      · subst index
        exact Or.inl (equal.symm.trans stored)
      · exact Or.inr ⟨index, notDeleted, by simpa [Function.update, same] using equal⟩

/-- Initial staging replaces only the removed dense ordinal by an out-of-
range sentinel. Existing occupancy is exactly the remaining rows plus hole. -/
theorem covered_initial (slots : List Nat) (deleted : Fin slots.length) (capacity slot : Nat) :
    Covered (Function.update (fun index : Fin slots.length => slots.get index) deleted capacity) deleted (slots.get deleted) slot ↔ slot ∈ slots := by
  classical
  constructor
  · rintro (same | ⟨index, active, equal⟩)
    · rw [same]
      exact List.get_mem slots deleted
    · have actual : slots.get index = slot := by simpa [Function.update, active] using equal
      rw [← actual]
      exact List.get_mem slots index
  · intro member
    obtain ⟨index, actual⟩ := List.mem_iff_get.mp member
    by_cases same : index = deleted
    · subst index
      exact Or.inl actual.symm
    · exact Or.inr ⟨index, same, by simpa [Function.update, same] using actual⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.entries_update_injective
#print axioms InitECandidate.Solver.MutableTable.Delete.entries_update_fresh
#print axioms InitECandidate.Solver.MutableTable.Delete.covered_update
#print axioms InitECandidate.Solver.MutableTable.Delete.covered_initial
