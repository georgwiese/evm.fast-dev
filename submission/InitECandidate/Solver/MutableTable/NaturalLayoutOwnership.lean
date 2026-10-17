import InitECandidate.Solver.MutableTable.NaturalLayoutSlots

namespace InitECandidate.Solver.MutableTable.NaturalLayout
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem plain_cell (plan : Plan) (pool : Pool) (index : BitVec 64) :
    cell plan pool 0 + index = cell plan pool index.toNat := by
  simpa only [BitVec.mul_one, Nat.mul_one] using scaled_cell plan pool index 1

theorem constant_cell (plan : Plan) (pool : Pool) (offset : Nat) :
    cell plan pool 0 + BitVec.ofNat 64 offset = cell plan pool offset := offset_cell plan pool offset

theorem word_offset_inside (kind : KeyHash.Kind) (plan : Plan) (pool : Pool) (index : Nat)
    (wordPool : pool = .values ∨ pool = .order ∨ pool = .position) (inside : index < plan.capacity) :
    index * 8 < size kind plan pool := by
  rcases wordPool with rfl | rfl | rfl <;> dsimp [size] <;> omega

theorem used_offset_inside (kind : KeyHash.Kind) (plan : Plan) (index : Nat) (inside : index < plan.capacity) :
    index < size kind plan .used := by
  have high := (rounded_bounds plan.capacity).1
  change index < rounded plan.capacity
  omega

/-- A copy to any actual key slot preserves every separate header cell,
both for byte accesses and for the aligned words used by memcpy. -/
theorem header_key_away (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (query index : BitVec 64)
    (inside : index.toNat < plan.capacity) (headerOffset : Nat) (headerInside : headerOffset < 72) :
    CopyGeneral.Away ((parameters kind plan query).keys + index * (parameters kind plan query).stride)
      (cell plan .header headerOffset) (KeyHash.keySize kind) := by
  intro offset byteInside
  have addressInside := slot_inside kind plan index.toNat offset inside byteInside
  constructor
  · rw [slot_byte]
    exact separate kind plan valid .header .keys (by decide) headerOffset _ headerInside addressInside
  · rw [slot_byte, byte_cell kind plan valid .keys _ addressInside]
    exact separate kind plan valid .header .keys (by decide) headerOffset _ headerInside (by omega)

/-- Actual source-domain mappings and all header protection required by raw
insertion are derived from six physical owned pools. No per-slot mapping or
copy/write separation oracle is needed at the caller. Applies after array
relocation as well as fresh construction. -/
theorem slot_data (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (query index count : BitVec 64)
    (inside : index.toNat < plan.capacity) (countInside : count.toNat < plan.capacity) :
    Insert.SlotData InitE.ordinaryDomain (parameters kind plan query)
      (cell plan .header 0) (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) count index (KeyHash.keySize kind) := by
  have valueInside := word_offset_inside kind plan .values index.toNat (Or.inl rfl) inside
  have orderInside := word_offset_inside kind plan .order count.toNat (Or.inr (Or.inl rfl)) countInside
  have positionInside := word_offset_inside kind plan .position index.toNat (Or.inr (Or.inr rfl)) inside
  have usedInside := used_offset_inside kind plan index.toNat inside
  refine ⟨slot_fits kind plan valid query index inside, slot_mapped kind plan valid query index inside,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [scaled_cell]
    exact mapped kind plan valid .values _ valueInside (by omega)
  · change InitE.ordinaryDomain (panByteAlignHOL (width := 64) (cell plan .used 0 + index))
    rw [plain_cell]
    exact byte_mapped kind plan valid .used index.toNat usedInside
  · rw [scaled_cell]
    exact mapped kind plan valid .order _ orderInside (by omega)
  · rw [scaled_cell]
    exact mapped kind plan valid .position _ positionInside (by omega)
  · rw [constant_cell, scaled_cell]
    exact separate kind plan valid .header .values (by decide) 24 _ (by change 24 < 72; decide) valueInside
  · change cell plan .header 0 + 24#64 ≠ panByteAlignHOL (width := 64) (cell plan .used 0 + index)
    rw [constant_cell, plain_cell, byte_cell kind plan valid .used index.toNat usedInside]
    exact separate kind plan valid .header .used (by decide) 24 _ (by change 24 < 72; decide) (by omega)
  · rw [constant_cell]
    exact header_key_away kind plan valid query index inside 40 (by decide)
  · rw [constant_cell]
    exact header_key_away kind plan valid query index inside 24 (by decide)

end InitECandidate.Solver.MutableTable.NaturalLayout

#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.plain_cell
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.constant_cell
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.word_offset_inside
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.used_offset_inside
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.header_key_away
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.slot_data
