import InitECandidate.Solver.MutableTable.MemoryModel
import InitECandidate.Solver.MutableTable.NaturalLayoutFrame
import InitECandidate.Solver.MutableTable.InsertGeneralFrame
import InitECandidate.Solver.MutableTable.InsertGeneralCall

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

def insertedMemory (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan)
    (query index count value : BitVec 64) : WordWrites.Memory :=
  Insert.generalResultMemory memory be (KeyHash.keySize kind) (parameters kind plan query)
    (cell plan .header 0) (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) index count value

/-- Exact untouched-header frame of actual generic insertion, with every
copy/value/used/order/position/count separation derived from pool geometry. -/
theorem inserted_header_away (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (query index count value : BitVec 64)
    (inside : index.toNat < plan.capacity) (countInside : count.toNat < plan.capacity)
    (offset : Nat) (headerInside : offset < 72) (notCount : offset ≠ 24) :
    insertedMemory memory be kind plan query index count value (cell plan .header offset) = memory (cell plan .header offset) := by
  have valueInside := word_offset_inside kind plan .values index.toNat (Or.inl rfl) inside
  have orderInside := word_offset_inside kind plan .order count.toNat (Or.inr (Or.inl rfl)) countInside
  have positionInside := word_offset_inside kind plan .position index.toNat (Or.inr (Or.inr rfl)) inside
  have usedInside := used_offset_inside kind plan index.toNat inside
  have valueAway : cell plan .header offset ≠ cell plan .values 0 + index * 8#64 := by
    rw [scaled_cell]
    exact separate kind plan valid .header .values (by decide) offset _ headerInside valueInside
  have usedAway : cell plan .header offset ≠ panByteAlignHOL (width := 64) ((parameters kind plan query).used + index) := by
    change cell plan .header offset ≠ panByteAlignHOL (width := 64) (cell plan .used 0 + index)
    rw [plain_cell, byte_cell kind plan valid .used index.toNat usedInside]
    exact separate kind plan valid .header .used (by decide) offset _ headerInside (by omega)
  have metaAway : cell plan .header offset ∉ (Insert.countWrites (cell plan .header 0) (cell plan .order 0) (cell plan .position 0) index count).map Prod.fst := by
    simp only [Insert.countWrites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true, Prod.fst]
    rw [scaled_cell, scaled_cell, constant_cell]
    exact ⟨separate kind plan valid .header .order (by decide) offset _ headerInside orderInside,
      separate kind plan valid .header .position (by decide) offset _ headerInside positionInside,
      cell_injective kind plan valid .header offset 24 headerInside (by change 24 < 72; decide) notCount⟩
  exact Insert.general_result_away memory be (KeyHash.keySize kind) (parameters kind plan query)
    (cell plan .header 0) (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) index count value (cell plan .header offset)
    (header_key_away kind plan valid query index inside offset headerInside) valueAway usedAway metaAway

/-- Actual insertion preserves all nine header meanings and performs exactly
the physical count increment. This is representation preservation, not a
logical dictionary specification or an assumed mutation execution. -/
theorem Header.after_insert (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (query index count value : BitVec 64)
    (inside : index.toNat < plan.capacity) (countInside : count.toNat < plan.capacity)
    (header : Header memory kind plan count) :
    Header (insertedMemory memory be kind plan query index count value) kind plan (count + 1#64) := by
  have kept (offset : Nat) (headerInside : offset < 72) (notCount : offset ≠ 24) (stored : BitVec 64)
      (member : (offset, stored) ∈ headerEntries kind plan count) :
      insertedMemory memory be kind plan query index count value (cell plan .header offset) = .word stored :=
    (inserted_header_away memory be kind plan valid query index count value inside countInside offset headerInside notCount).trans (header offset stored member)
  intro offset stored member
  simp only [headerEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact kept 0 (by decide) (by decide) _ (by simp [headerEntries])
  · exact kept 8 (by decide) (by decide) _ (by simp [headerEntries])
  · exact kept 16 (by decide) (by decide) _ (by simp [headerEntries])
  · have actual := Insert.general_result_count memory be (KeyHash.keySize kind) (parameters kind plan query)
      (cell plan .header 0) (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) index count value
    rw [constant_cell] at actual
    exact actual
  · exact kept 32 (by decide) (by decide) _ (by simp [headerEntries])
  · exact kept 40 (by decide) (by decide) _ (by simp [headerEntries])
  · exact kept 48 (by decide) (by decide) _ (by simp [headerEntries])
  · exact kept 56 (by decide) (by decide) _ (by simp [headerEntries])
  · exact kept 64 (by decide) (by decide) _ (by simp [headerEntries])

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.inserted_header_away
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Header.after_insert
