import InitECandidate.Solver.MutableTable.DeleteSlots
import Mathlib.Data.List.FinRange

namespace InitECandidate.Solver.MutableTable.Delete

/-- The original final swap keeps each ordinal before count-1, redirecting
the removed ordinal to the old last entry. No program state is modified here. -/
def remainingOrdinal {count : Nat} (deleted : Fin count) (index : Fin (count - 1)) : Fin count :=
  if index.val = deleted.val then ⟨count - 1, by have := deleted.isLt; omega⟩
  else ⟨index.val, by have := index.isLt; omega⟩

theorem remaining_active {count : Nat} (deleted : Fin count) (index : Fin (count - 1)) : remainingOrdinal deleted index ≠ deleted := by
  intro equal
  have numeric := congrArg Fin.val equal
  have high := index.isLt
  by_cases same : index.val = deleted.val
  · simp only [remainingOrdinal, if_pos same] at numeric
    omega
  · simp only [remainingOrdinal, if_neg same] at numeric
    exact same numeric

theorem remaining_injective {count : Nat} (deleted : Fin count) : Function.Injective (remainingOrdinal deleted) := by
  intro first second equal
  have numeric := congrArg Fin.val equal
  have firstHigh := first.isLt
  have secondHigh := second.isLt
  by_cases atFirst : first.val = deleted.val <;> by_cases atSecond : second.val = deleted.val
  · exact Fin.ext (by omega)
  · simp only [remainingOrdinal, if_pos atFirst, if_neg atSecond] at numeric
    omega
  · simp only [remainingOrdinal, if_neg atFirst, if_pos atSecond] at numeric
    omega
  · apply Fin.ext
    simpa only [remainingOrdinal, if_neg atFirst, if_neg atSecond] using numeric

theorem remaining_surjective {count : Nat} (deleted ordinal : Fin count) (active : ordinal ≠ deleted) :
    ∃ index : Fin (count - 1), remainingOrdinal deleted index = ordinal := by
  have ordinalHigh := ordinal.isLt
  have deletedHigh := deleted.isLt
  by_cases last : ordinal.val = count - 1
  · have different : deleted.val ≠ count - 1 := by intro same; apply active; exact Fin.ext (by omega)
    let index : Fin (count - 1) := ⟨deleted.val, by omega⟩
    refine ⟨index, Fin.ext ?_⟩
    simpa only [remainingOrdinal, index, ↓reduceIte] using last.symm
  · have different : ordinal.val ≠ deleted.val := fun same => active (Fin.ext same)
    let index : Fin (count - 1) := ⟨ordinal.val, by omega⟩
    refine ⟨index, Fin.ext ?_⟩
    simp only [remainingOrdinal, index, if_neg different]

def finalSlots {count : Nat} (entries : Fin count → Nat) (deleted : Fin count) : List Nat :=
  List.ofFn (fun index : Fin (count - 1) => entries (remainingOrdinal deleted index))

theorem final_length {count : Nat} (entries : Fin count → Nat) (deleted : Fin count) : (finalSlots entries deleted).length = count - 1 := by
  simp [finalSlots]

theorem final_distinct {count : Nat} (entries : Fin count → Nat) (deleted : Fin count) (distinct : Function.Injective entries) :
    (finalSlots entries deleted).Nodup := List.nodup_ofFn_ofInjective (distinct.comp (remaining_injective deleted))

theorem final_member {count : Nat} (entries : Fin count → Nat) (deleted : Fin count) (slot : Nat) :
    slot ∈ finalSlots entries deleted ↔ ∃ ordinal, ordinal ≠ deleted ∧ entries ordinal = slot := by
  simp only [finalSlots, List.mem_ofFn]
  constructor
  · rintro ⟨index, same⟩
    exact ⟨remainingOrdinal deleted index, remaining_active deleted index, same⟩
  · rintro ⟨ordinal, active, same⟩
    obtain ⟨index, equal⟩ := remaining_surjective deleted ordinal active
    exact ⟨index, by rw [equal]; exact same⟩

theorem final_get {count : Nat} (entries : Fin count → Nat) (deleted : Fin count) (index : Fin (count - 1)) :
    (finalSlots entries deleted).get ⟨index.val, by rw [final_length]; exact index.isLt⟩ = entries (remainingOrdinal deleted index) := by
  simp [finalSlots, List.get_eq_getElem]

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.remaining_active
#print axioms InitECandidate.Solver.MutableTable.Delete.remaining_injective
#print axioms InitECandidate.Solver.MutableTable.Delete.remaining_surjective
#print axioms InitECandidate.Solver.MutableTable.Delete.final_length
#print axioms InitECandidate.Solver.MutableTable.Delete.final_distinct
#print axioms InitECandidate.Solver.MutableTable.Delete.final_member
#print axioms InitECandidate.Solver.MutableTable.Delete.final_get
