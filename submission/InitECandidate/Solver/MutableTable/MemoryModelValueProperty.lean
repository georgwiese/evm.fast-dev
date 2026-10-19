import InitECandidate.Solver.MutableTable.MemoryModelInsertFields
import InitECandidate.Solver.MutableTable.OccupiedValueProperty

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- The key copy, used-byte update and metadata writes in an actual insertion
leave value words with exactly the effect of its single value store. -/
theorem inserted_value_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (query index count value slot : BitVec 64) (inside : index.toNat < plan.capacity)
    (countInside : count.toNat < plan.capacity) (slotInside : slot.toNat < plan.capacity) :
    insertedMemory source.memory source.be kind plan query index count value (cell plan .values 0+slot*8#64) =
      valueMemory source.memory plan index value (cell plan .values 0+slot*8#64) := by
  have extent := word_offset_inside kind plan .values slot.toNat (Or.inl rfl) slotInside
  have usedInside := used_offset_inside kind plan index.toNat inside
  have apart : cell plan .values (slot.toNat*8) ≠
      panByteAlignHOL (width:=64) (cell plan .used 0+index) := by
    rw [plain_cell, byte_cell kind plan valid .used index.toNat usedInside]
    exact separate kind plan valid .values .used (by decide) _ _ extent (by omega)
  change metadataMemory
    (ByteStore.write (copiedValueMemory source.memory source.be kind plan query index value)
      (cell plan .used 0+index) 1) plan index count _ = _
  rw [scaled_cell, metadata_pool_away _ kind plan valid index count inside countInside
    .values (by decide) (by decide) (by decide) _ extent]
  simp only [ByteStore.write, StoreWord.put, if_neg apart]
  change StoreWord.put _ _ value _ = StoreWord.put _ _ value _
  by_cases same : cell plan .values (slot.toNat*8)=cell plan .values 0+index*8#64
  · simp only [StoreWord.put, if_pos same]
  · simp only [StoreWord.put, if_neg same]
    exact CopyGeneral.resultMemory_away source.memory source.be query _ _ _
      (pool_key_away kind plan valid query index inside .values (by decide) _ extent)

theorem values_after_update (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : Plan) (index value : BitVec 64) (slots : List Nat) (property : BitVec 64 → Prop)
    (values : Get.OccupiedValuesHave source (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) slots property)
    (owned : property value) :
    Get.OccupiedValuesHave {source with memory:=valueMemory source.memory plan index value}
      (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) slots property :=
  values.word_update source _ _ _ _ slots property owned

/-- An actual insertion extends ownership only to the newly occupied slot;
it imposes no condition on uninitialized unused values. -/
theorem values_after_insert (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (query index count value : BitVec 64) (inside : index.toNat < plan.capacity)
    (countInside : count.toNat < plan.capacity) (slots : List Nat) (property : BitVec 64 → Prop)
    (values : Get.OccupiedValuesHave source (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) slots property)
    (owned : property value) :
    Get.OccupiedValuesHave {source with memory:=insertedMemory source.memory source.be kind plan query index count value}
      (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) (slots++[index.toNat]) property := by
  have updated := values.append_word source _ _ index value slots property owned
  apply updated.of_agreement _ _ _ _ _ _
  intro slot bounded member
  have slotInside : slot.toNat < plan.capacity := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity_small kind plan valid)] using bounded
  exact inserted_value_cell source kind plan valid query index count value slot inside countInside slotInside

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.inserted_value_cell
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.values_after_update
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.values_after_insert
