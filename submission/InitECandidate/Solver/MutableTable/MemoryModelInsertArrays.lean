import InitECandidate.Solver.MutableTable.MemoryModelInsertFields

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem metadata_order (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (index count : BitVec 64) (inside : index.toNat < plan.capacity) (offset : Nat) (orderInside : offset < size kind plan .order) :
    metadataMemory memory plan index count (cell plan .order offset) =
      if cell plan .order offset = cell plan .order 0 + count * 8#64 then .word index else memory (cell plan .order offset) := by
  have positionAway : cell plan .order offset ≠ cell plan .position 0 + index * 8#64 := by
    rw [scaled_cell]
    exact separate kind plan valid .order .position (by decide) offset _ orderInside
      (word_offset_inside kind plan .position index.toNat (Or.inr (Or.inr rfl)) inside)
  have headerAway : cell plan .order offset ≠ cell plan .header 0 + 24#64 := by
    rw [constant_cell]
    exact separate kind plan valid .order .header (by decide) offset 24 orderInside (by change 24 < 72; decide)
  simp only [metadataMemory, Insert.countWrites, WordWrites.write, StoreWord.put, if_neg headerAway, if_neg positionAway]

theorem metadata_position (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (index count : BitVec 64) (countInside : count.toNat < plan.capacity) (offset : Nat) (positionInside : offset < size kind plan .position) :
    metadataMemory memory plan index count (cell plan .position offset) =
      if cell plan .position offset = cell plan .position 0 + index * 8#64 then .word count else memory (cell plan .position offset) := by
  have orderAway : cell plan .position offset ≠ cell plan .order 0 + count * 8#64 := by
    rw [scaled_cell]
    exact separate kind plan valid .position .order (by decide) offset _ positionInside
      (word_offset_inside kind plan .order count.toNat (Or.inr (Or.inl rfl)) countInside)
  have headerAway : cell plan .position offset ≠ cell plan .header 0 + 24#64 := by
    rw [constant_cell]
    exact separate kind plan valid .position .header (by decide) offset 24 positionInside (by change 24 < 72; decide)
  simp only [metadataMemory, Insert.countWrites, WordWrites.write, StoreWord.put, if_neg headerAway, if_neg orderAway]

theorem indexed_cell_eq (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (pool : Pool)
    (wordPool : pool = .values ∨ pool = .order ∨ pool = .position) (slot : Nat) (index : BitVec 64)
    (slotInside : slot < plan.capacity) (inside : index.toNat < plan.capacity) :
    (cell plan pool (8 * slot) = cell plan pool 0 + index * 8#64) ↔ slot = index.toNat := by
  rw [scaled_cell]
  constructor
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    rw [number kind plan valid pool (8 * slot) (by simpa only [Nat.mul_comm 8] using word_offset_inside kind plan pool slot wordPool slotInside),
      number kind plan valid pool (index.toNat * 8) (word_offset_inside kind plan pool index.toNat wordPool inside)] at numeric
    omega
  · intro equal
    rw [equal, Nat.mul_comm 8]

/-- Exact dense-order array effect of the full original insertion. -/
theorem inserted_order (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (query index count value : BitVec 64) (inside : index.toNat < plan.capacity) (countInside : count.toNat < plan.capacity)
    (slot : Nat) (slotInside : slot < plan.capacity) :
    insertedMemory memory be kind plan query index count value (cell plan .order (8 * slot)) =
      if slot = count.toNat then .word index else memory (cell plan .order (8 * slot)) := by
  have bounded : 8 * slot < size kind plan .order := by simpa only [Nat.mul_comm 8] using word_offset_inside kind plan .order slot (Or.inr (Or.inl rfl)) slotInside
  change metadataMemory (ByteStore.write (copiedValueMemory memory be kind plan query index value) (cell plan .used 0 + index) 1) plan index count _ = _
  rw [metadata_order _ kind plan valid index count inside _ bounded]
  simp only [indexed_cell_eq kind plan valid .order (Or.inr (Or.inl rfl)) slot count slotInside countInside,
    flag_pool_away memory be kind plan valid query index value inside .order (by decide) (by decide) (by decide) _ bounded]

/-- Exact inverse-position array effect of the full original insertion. -/
theorem inserted_position (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (query index count value : BitVec 64) (inside : index.toNat < plan.capacity) (countInside : count.toNat < plan.capacity)
    (slot : Nat) (slotInside : slot < plan.capacity) :
    insertedMemory memory be kind plan query index count value (cell plan .position (8 * slot)) =
      if slot = index.toNat then .word count else memory (cell plan .position (8 * slot)) := by
  have bounded : 8 * slot < size kind plan .position := by simpa only [Nat.mul_comm 8] using word_offset_inside kind plan .position slot (Or.inr (Or.inr rfl)) slotInside
  change metadataMemory (ByteStore.write (copiedValueMemory memory be kind plan query index value) (cell plan .used 0 + index) 1) plan index count _ = _
  rw [metadata_position _ kind plan valid index count countInside _ bounded]
  simp only [indexed_cell_eq kind plan valid .position (Or.inr (Or.inr rfl)) slot index slotInside inside,
    flag_pool_away memory be kind plan valid query index value inside .position (by decide) (by decide) (by decide) _ bounded]

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.metadata_order
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.metadata_position
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.indexed_cell_eq
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.inserted_order
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.inserted_position
