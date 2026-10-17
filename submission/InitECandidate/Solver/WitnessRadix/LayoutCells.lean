import InitECandidate.Solver.WitnessRadix.LayoutSeparation

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

def IncomingOffset (layout : Layout) (allocated : Nat) : Pool → Nat → Prop
  | .header, offset => offset = 24
  | .keys, offset => ∃ node < allocated, ∃ field, (field = 1 ∨ field = 2) ∧
      offset = 32 * layout.count + 24 * node + 8 * field
  | _, _ => False

theorem incoming_write (layout : Layout) (allocated : Nat) (inside : allocated < layout.count)
    (entry : Address) (incoming : IncomingOffset layout allocated entry.1 entry.2) :
    WriteOffset layout entry.1 entry.2 := by
  obtain ⟨pool, offset⟩ := entry
  cases pool with
  | header => exact incoming
  | keys =>
      obtain ⟨node, old, field, fieldBound, value⟩ := incoming
      exact ⟨node, by omega, field, by rcases fieldBound with rfl | rfl <;> decide, value⟩
  | vals | primary | backup | records => exact False.elim incoming

def allocationAddresses (layout : Layout) (allocated depth : Nat) (destination : Address) : List Address :=
  [(.keys, 32 * layout.count + 24 * allocated),
   (.keys, 32 * layout.count + 24 * allocated + 8),
   (.keys, 32 * layout.count + 24 * allocated + 16), destination,
   (.primary, 8 * layout.count + 8 * depth), (.backup, 8 * layout.count + 8 * depth),
   (.vals, 8 * layout.count + 8 * depth)]

theorem allocation_addresses_distinct (layout : Layout) (allocated depth : Nat) (destination : Address)
    (incoming : IncomingOffset layout allocated destination.1 destination.2) :
    (allocationAddresses layout allocated depth destination).Nodup := by
  obtain ⟨pool, offset⟩ := destination
  cases pool with
  | header =>
      rcases incoming with rfl
      simp [allocationAddresses, List.nodup_cons, List.mem_cons]
  | keys =>
      obtain ⟨node, old, field, fieldBound, rfl⟩ := incoming
      rcases fieldBound with rfl | rfl <;>
        simp [allocationAddresses, List.nodup_cons, List.mem_cons] <;> omega
  | vals | primary | backup | records => exact False.elim incoming

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.addresses_nodup
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.allocation_addresses_distinct
