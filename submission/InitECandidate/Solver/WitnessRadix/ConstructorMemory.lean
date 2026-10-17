import InitECandidate.Solver.WitnessRadix.ConstructorLayout

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

theorem write_append (memory : WordWrites.Memory) (left right : List (BitVec 64 × BitVec 64)) :
    WordWrites.write memory (left ++ right) = WordWrites.write (WordWrites.write memory left) right := by
  induction left generalizing memory with
  | nil => rfl
  | cons entry rest ih => exact ih _

theorem suffix_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (index : Nat) (words : Fin 4 → BitVec 64) :
    (storesPost (copyPost source layout.keys (BitVec.ofNat 64 index) words)
      layout.vals layout.primary layout.records (BitVec.ofNat 64 index)).memory =
      WordWrites.write source.memory (writes layout index words) := by
  exact (write_append _ _ _).symm

/-- All six actual stores have a concrete pool/offset footprint. -/
theorem written_cell (layout : Layout) (index : Nat) (words : Fin 4 → BitVec 64)
    (entry : Address) (member : entry ∈ writeAddresses index) :
    ∃ value, (address layout entry, value) ∈ writes layout index words := by
  have addressMember : address layout entry ∈ (writes layout index words).map Prod.fst := by
    rw [write_cells]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  obtain ⟨pair, pairMember, pairAddress⟩ := List.mem_map.mp addressMember
  refine ⟨pair.2, ?_⟩
  have pairEq : pair = (address layout entry, pair.2) := Prod.ext pairAddress rfl
  rw [pairEq] at pairMember
  exact pairMember

/-- An arbitrary allocated word survives the whole suffix whenever its
virtual pool/offset address is outside the six stores. -/
theorem memory_away (memory : WordWrites.Memory) (layout : Layout) (valid : Valid layout)
    (index : Nat) (inside : index < layout.count) (words : Fin 4 → BitVec 64)
    (entry : Address) (bound : entry.2 < size layout entry.1)
    (absent : entry ∉ writeAddresses index) :
    WordWrites.write memory (writes layout index words) (address layout entry) = memory (address layout entry) := by
  apply WordWrites.write_away
  rw [write_cells]
  intro member
  obtain ⟨other, otherMember, same⟩ := List.mem_map.mp member
  have otherBound := write_bounds layout valid index inside other otherMember
  have equal := address_injective layout valid other entry (by omega) bound same
  exact absent (equal ▸ otherMember)

theorem record_value_member (layout : Layout) (index : Nat) (words : Fin 4 → BitVec 64) :
    (cell layout .vals (8 * index), record layout index) ∈ writes layout index words := by
  apply List.mem_append_right
  simp [recordWrites, vals_cell, record_cell]

theorem ordinal_member (layout : Layout) (index : Nat) (words : Fin 4 → BitVec 64) :
    (cell layout .primary (8 * index), BitVec.ofNat 64 index) ∈ writes layout index words := by
  apply List.mem_append_right
  simp [recordWrites, primary_cell]

theorem hash_member (layout : Layout) (index : Nat) (words : Fin 4 → BitVec 64) (limb : Fin 4) :
    (cell layout .keys (32 * index + 8 * limb.val), words limb) ∈ writes layout index words := by
  apply List.mem_append_left
  rw [← hash_limb_cell]
  exact Copy32.write_member _ words limb

theorem record_value_written (memory : WordWrites.Memory) (layout : Layout) (valid : Valid layout)
    (index : Nat) (inside : index < layout.count) (words : Fin 4 → BitVec 64) :
    WordWrites.write memory (writes layout index words) (cell layout .vals (8 * index)) = .word (record layout index) :=
  WordWrites.write_unique memory _ _ (writes_distinct layout valid index inside words) (record_value_member layout index words)

theorem ordinal_written (memory : WordWrites.Memory) (layout : Layout) (valid : Valid layout)
    (index : Nat) (inside : index < layout.count) (words : Fin 4 → BitVec 64) :
    WordWrites.write memory (writes layout index words) (cell layout .primary (8 * index)) = .word (BitVec.ofNat 64 index) :=
  WordWrites.write_unique memory _ _ (writes_distinct layout valid index inside words) (ordinal_member layout index words)

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.suffix_memory
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.memory_away
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.record_value_written
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.ordinal_written
