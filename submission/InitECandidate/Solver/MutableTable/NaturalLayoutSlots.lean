import InitECandidate.Solver.MutableTable.NaturalLayoutRelocated
import InitECandidate.Solver.MutableTable.InsertGeneralEntry

namespace InitECandidate.Solver.MutableTable.NaturalLayout
open Flapjack PanSemStateFiniteExact WitnessRadix

def parameters (kind : KeyHash.Kind) (plan : Plan) (query : BitVec 64) : Find.Parameters where
  capacity := BitVec.ofNat 64 plan.capacity
  keyLength := BitVec.ofNat 64 (KeyHash.keySize kind)
  stride := BitVec.ofNat 64 (stride kind)
  keys := cell plan .keys 0
  used := cell plan .used 0
  key := query

theorem scaled_cell (plan : Plan) (pool : Pool) (index : BitVec 64) (step : Nat) :
    cell plan pool 0 + index * BitVec.ofNat 64 step = cell plan pool (index.toNat * step) := by
  have indexWord : BitVec.ofNat 64 index.toNat = index := by simp
  calc
    _ = cell plan pool 0 + BitVec.ofNat 64 index.toNat * BitVec.ofNat 64 step := by rw [indexWord]
    _ = cell plan pool (index.toNat * step) := by simp only [cell, Nat.add_zero, BitVec.ofNat_add, BitVec.ofNat_mul]

theorem slot_byte (kind : KeyHash.Kind) (plan : Plan) (query index : BitVec 64) (offset : Nat) :
    byteAddress ((parameters kind plan query).keys + index * (parameters kind plan query).stride) offset =
      cell plan .keys (index.toNat * stride kind + offset) := by
  change byteAddress (cell plan .keys 0 + index * BitVec.ofNat 64 (stride kind)) offset = _
  rw [scaled_cell]
  simp only [byteAddress, cell, BitVec.ofNat_add, BitVec.add_assoc]

theorem slot_inside (kind : KeyHash.Kind) (plan : Plan) (index offset : Nat) (inside : index < plan.capacity)
    (byteInside : offset < KeyHash.keySize kind) : index * stride kind + offset < size kind plan .keys := by
  cases kind <;> dsimp [stride, KeyHash.keySize, size] at byteInside ⊢ <;> omega

theorem slot_extent (kind : KeyHash.Kind) (plan : Plan) (index : Nat) (inside : index < plan.capacity) :
    index * stride kind + KeyHash.keySize kind ≤ size kind plan .keys := by
  cases kind <;> dsimp [stride, KeyHash.keySize, size] <;> omega

theorem slot_fits (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (query index : BitVec 64)
    (inside : index.toNat < plan.capacity) :
    ((parameters kind plan query).keys + index * (parameters kind plan query).stride).toNat + KeyHash.keySize kind < 2 ^ 64 := by
  change (cell plan .keys 0 + index * BitVec.ofNat 64 (stride kind)).toNat + _ < _
  rw [scaled_cell, number kind plan valid .keys _ (by
    have nonempty : 0 < KeyHash.keySize kind := by cases kind <;> decide
    exact slot_inside kind plan _ 0 inside nonempty)]
  have extent := slot_extent kind plan index.toNat inside
  have upper := valid.upper .keys
  omega

theorem slot_mapped (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (query index : BitVec 64)
    (inside : index.toNat < plan.capacity) :
    ∀ offset < KeyHash.keySize kind, InitE.ordinaryDomain (panByteAlignHOL (width := 64)
      (byteAddress ((parameters kind plan query).keys + index * (parameters kind plan query).stride) offset)) := by
  intro offset byteInside
  rw [slot_byte]
  exact byte_mapped kind plan valid .keys _ (slot_inside kind plan _ _ inside byteInside)

end InitECandidate.Solver.MutableTable.NaturalLayout

#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.scaled_cell
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.slot_byte
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.slot_inside
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.slot_extent
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.slot_fits
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.slot_mapped
