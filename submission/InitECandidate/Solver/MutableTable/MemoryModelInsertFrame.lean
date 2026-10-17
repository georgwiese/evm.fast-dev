import InitECandidate.Solver.MutableTable.MemoryModelInsertFields

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Complete original insertion preserves a word outside its five arrays
and count field. This includes old rehash inputs and unrelated live objects. -/
theorem inserted_away (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (query index count value address : BitVec 64)
    (inside : index.toNat < plan.capacity) (countInside : count.toNat < plan.capacity)
    (arraysAway : ∀ pool : Pool, pool ≠ .header → ∀ offset < size kind plan pool, address ≠ cell plan pool offset)
    (countAway : address ≠ cell plan .header 24) :
    insertedMemory memory be kind plan query index count value address = memory address := by
  have copyAway : CopyGeneral.Away ((parameters kind plan query).keys + index * (parameters kind plan query).stride) address (KeyHash.keySize kind) := by
    intro offset byteInside
    have extent := slot_inside kind plan index.toNat offset inside byteInside
    constructor
    · rw [slot_byte]
      exact arraysAway .keys (by decide) _ extent
    · rw [slot_byte, byte_cell kind plan valid .keys _ extent]
      exact arraysAway .keys (by decide) _ (by omega)
  have valuesAway : address ≠ cell plan .values 0 + index * 8#64 := by
    rw [scaled_cell]
    exact arraysAway .values (by decide) _ (word_offset_inside kind plan .values index.toNat (Or.inl rfl) inside)
  have usedAway : address ≠ panByteAlignHOL (width := 64) ((parameters kind plan query).used + index) := by
    change address ≠ panByteAlignHOL (width := 64) (cell plan .used 0 + index)
    rw [plain_cell, byte_cell kind plan valid .used index.toNat (used_offset_inside kind plan index.toNat inside)]
    exact arraysAway .used (by decide) _ (by have := used_offset_inside kind plan index.toNat inside; omega)
  have metaAway : address ∉ (Insert.countWrites (cell plan .header 0) (cell plan .order 0) (cell plan .position 0) index count).map Prod.fst := by
    simp only [Insert.countWrites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true, Prod.fst]
    rw [scaled_cell, scaled_cell, constant_cell]
    exact ⟨arraysAway .order (by decide) _ (word_offset_inside kind plan .order count.toNat (Or.inr (Or.inl rfl)) countInside),
      arraysAway .position (by decide) _ (word_offset_inside kind plan .position index.toNat (Or.inr (Or.inr rfl)) inside), countAway⟩
  exact Insert.general_result_away memory be (KeyHash.keySize kind) (parameters kind plan query) (cell plan .header 0)
    (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) index count value address copyAway valuesAway usedAway metaAway

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.inserted_away
