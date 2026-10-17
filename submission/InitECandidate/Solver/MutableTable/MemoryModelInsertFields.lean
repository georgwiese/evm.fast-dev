import InitECandidate.Solver.MutableTable.MemoryModelInsertHeader
import InitECandidate.Solver.MutableTable.MemoryModelValue

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

def metadataMemory (memory : WordWrites.Memory) (plan : Plan) (index count : BitVec 64) : WordWrites.Memory :=
  WordWrites.write memory (Insert.countWrites (cell plan .header 0) (cell plan .order 0) (cell plan .position 0) index count)
def copiedValueMemory (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (query index value : BitVec 64) : WordWrites.Memory :=
  valueMemory (CopyGeneral.resultMemory memory be query ((parameters kind plan query).keys + index * (parameters kind plan query).stride) (KeyHash.keySize kind)) plan index value

/-- Actual final order/position/count writes preserve every other pool. -/
theorem metadata_pool_away (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (index count : BitVec 64) (inside : index.toNat < plan.capacity) (countInside : count.toNat < plan.capacity)
    (pool : Pool) (notOrder : pool ≠ .order) (notPosition : pool ≠ .position) (notHeader : pool ≠ .header)
    (offset : Nat) (poolInside : offset < size kind plan pool) :
    metadataMemory memory plan index count (cell plan pool offset) = memory (cell plan pool offset) := by
  apply WordWrites.write_away
  simp only [Insert.countWrites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true, Prod.fst]
  rw [scaled_cell, scaled_cell, constant_cell]
  exact ⟨separate kind plan valid pool .order notOrder offset _ poolInside (word_offset_inside kind plan .order count.toNat (Or.inr (Or.inl rfl)) countInside),
    separate kind plan valid pool .position notPosition offset _ poolInside (word_offset_inside kind plan .position index.toNat (Or.inr (Or.inr rfl)) inside),
    separate kind plan valid pool .header notHeader offset 24 poolInside (by change 24 < 72; decide)⟩

theorem copied_value_pool_away (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (query index value : BitVec 64) (inside : index.toNat < plan.capacity) (pool : Pool) (notKeys : pool ≠ .keys) (notValues : pool ≠ .values)
    (offset : Nat) (poolInside : offset < size kind plan pool) :
    copiedValueMemory memory be kind plan query index value (cell plan pool offset) = memory (cell plan pool offset) := by
  rw [copiedValueMemory, value_pool_away _ kind plan valid index value inside pool notValues offset poolInside]
  exact CopyGeneral.resultMemory_away memory be query _ _ _ (pool_key_away kind plan valid query index inside pool notKeys offset poolInside)

theorem flag_pool_away (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (query index value : BitVec 64) (inside : index.toNat < plan.capacity) (pool : Pool)
    (notKeys : pool ≠ .keys) (notValues : pool ≠ .values) (notUsed : pool ≠ .used)
    (offset : Nat) (poolInside : offset < size kind plan pool) :
    ByteStore.write (copiedValueMemory memory be kind plan query index value) (cell plan .used 0 + index) 1 (cell plan pool offset) = memory (cell plan pool offset) := by
  have usedInside := used_offset_inside kind plan index.toNat inside
  have apart : cell plan pool offset ≠ panByteAlignHOL (width := 64) (cell plan .used 0 + index) := by
    rw [plain_cell, byte_cell kind plan valid .used index.toNat usedInside]
    exact separate kind plan valid pool .used notUsed offset _ poolInside (by omega)
  simp only [ByteStore.write, StoreWord.put, if_neg apart]
  exact copied_value_pool_away memory be kind plan valid query index value inside pool notKeys notValues offset poolInside

/-- Actual used-byte effect of the complete generic insertion, including
all bytes sharing the same physical word. Exactly the selected byte becomes1;
all other used bytes retain their original values. -/
theorem inserted_used (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (query index count value slot : BitVec 64) (inside : index.toNat < plan.capacity) (countInside : count.toNat < plan.capacity)
    (slotInside : slot.toNat < plan.capacity) :
    Find.usedByte {source with memory := insertedMemory source.memory source.be kind plan query index count value} (parameters kind plan 0#64) slot =
      if slot = index then some 1 else Find.usedByte source (parameters kind plan 0#64) slot := by
  let p := parameters kind plan 0#64
  let before := {source with memory := copiedValueMemory source.memory source.be kind plan query index value}
  let flagged := {before with memory := ByteStore.write before.memory (cell plan .used 0 + index) 1}
  let post := {source with memory := insertedMemory source.memory source.be kind plan query index count value}
  have slotExtent := used_offset_inside kind plan slot.toNat slotInside
  have queryCell : panByteAlignHOL (width := 64) (p.used + slot) = cell plan .used (8 * (slot.toNat / 8)) := by
    change panByteAlignHOL (width := 64) (cell plan .used 0 + slot) = _
    rw [plain_cell, byte_cell kind plan valid .used slot.toNat slotExtent]
  have finalCell : post.memory (panByteAlignHOL (width := 64) (p.used + slot)) = flagged.memory (panByteAlignHOL (width := 64) (p.used + slot)) := by
    rw [queryCell]
    exact metadata_pool_away flagged.memory kind plan valid index count inside countInside .used (by decide) (by decide) (by decide) _ (by omega)
  have originalCell : before.memory (panByteAlignHOL (width := 64) (p.used + slot)) = source.memory (panByteAlignHOL (width := 64) (p.used + slot)) := by
    rw [queryCell]
    exact copied_value_pool_away source.memory source.be kind plan valid query index value inside .used (by decide) (by decide) _ (by omega)
  have beforeRead := Find.usedByte_of_cell before source p slot rfl rfl originalCell
  have writeMapped : before.memaddrs (panByteAlignHOL (width := 64) (cell plan .used 0 + index)) := by
    change source.memaddrs _
    rw [domain, plain_cell]
    exact byte_mapped kind plan valid .used index.toNat (used_offset_inside kind plan index.toNat inside)
  have written : Find.usedByte flagged p slot = if slot = index then some 1 else Find.usedByte before p slot := by
    have actual := ByteStore.read_write before (cell plan .used 0 + index) (cell plan .used 0 + slot) 1 little writeMapped
    simpa only [Find.usedByte, p, parameters, BitVec.add_right_inj] using actual
  rw [Find.usedByte_of_cell post flagged p slot rfl rfl finalCell, written, beforeRead]

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.metadata_pool_away
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.copied_value_pool_away
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.flag_pool_away
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.inserted_used
