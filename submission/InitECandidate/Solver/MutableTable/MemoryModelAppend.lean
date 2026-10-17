import InitECandidate.Solver.MutableTable.MemoryModelInsertArrays
import Mathlib.Data.List.Nodup

namespace InitECandidate.Solver.MutableTable.MemoryModel

/-- Old dense-order entries keep the same indices after one appended slot. -/
theorem append_get_old (slots : List Nat) (slot : Nat) (index : Fin (slots ++ [slot]).length) (old : index.val < slots.length) :
    (slots ++ [slot]).get index = slots.get ⟨index.val, old⟩ := by
  simp only [List.get_eq_getElem]
  exact List.getElem_append_left old

/-- The new final dense-order entry is the appended physical slot. -/
theorem append_get_new (slots : List Nat) (slot : Nat) (index : Fin (slots ++ [slot]).length) (last : index.val = slots.length) :
    (slots ++ [slot]).get index = slot := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (by omega)]
  simp [last]

theorem append_distinct (slots : List Nat) (slot : Nat) (distinct : slots.Nodup) (fresh : slot ∉ slots) :
    (slots ++ [slot]).Nodup := by
  simpa only [List.concat_eq_append] using List.Nodup.concat fresh distinct

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.append_get_old
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.append_get_new
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.append_distinct
