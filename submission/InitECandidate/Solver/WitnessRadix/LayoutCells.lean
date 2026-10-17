import InitECandidate.Solver.WitnessRadix.BackingLayout

namespace InitECandidate.Solver.WitnessRadix.BackingLayout

abbrev Address := Pool × Nat
def address (layout : Layout) (value : Address) : BitVec 64 := cell layout value.1 value.2

theorem address_injective (layout : Layout) (valid : Valid layout) (left right : Address)
    (leftBound : left.2 < size layout left.1) (rightBound : right.2 < size layout right.1)
    (same : address layout left = address layout right) : left = right := by
  obtain ⟨lp, lo⟩ := left
  obtain ⟨rp, ro⟩ := right
  by_cases pools : lp = rp
  · subst rp
    by_cases offsets : lo = ro
    · subst ro; rfl
    · exact False.elim (cell_injective layout valid lp lo ro leftBound rightBound offsets same)
  · exact False.elim (valid.separate lp rp pools lo leftBound ro rightBound same)

theorem addresses_nodup (layout : Layout) (valid : Valid layout) (input : List Address)
    (bounds : ∀ entry ∈ input, entry.2 < size layout entry.1) (distinct : input.Nodup) :
    (input.map (address layout)).Nodup := by
  induction input with
  | nil => simp
  | cons entry rest ih =>
      have unique := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      refine ⟨?_, ih (fun next member => bounds next (List.mem_cons_of_mem entry member)) unique.2⟩
      intro member
      obtain ⟨other, otherMember, same⟩ := List.mem_map.mp member
      have equal := address_injective layout valid other entry
        (bounds other (List.mem_cons_of_mem entry otherMember)) (bounds entry (by simp)) same
      exact unique.1 (equal ▸ otherMember)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.addresses_nodup
