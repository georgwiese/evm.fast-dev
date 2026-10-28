import InitECandidate.Solver.Input.CurrentTable.SlotGeometry
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Model

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem slot_number (base index cap : BitVec 64) (width : Nat)
    (array : AllocatedBytes.Arena base (width*(cap.toNat+1))) (inside : index.toNat ≤ cap.toNat) :
    (slot base index width).toNat = base.toNat+width*index.toNat := by
  rw [slot_address]
  apply byteAddress_toNat
  have extent : width*index.toNat ≤ width*(cap.toNat+1) := Nat.mul_le_mul_left width (by omega)
  have upper := array.upper
  omega

/-- The exact actual32-byte node cell, with both source-word multiplication
and address addition proved nonwrapping from the real allocated array. -/
theorem cell_number (base index cap : BitVec 64) (offset : Nat)
    (array : AllocatedBytes.Arena base (32*(cap.toNat+1))) (inside : index.toNat ≤ cap.toNat) (small : offset < 32) :
    (FindLeaf.cell base index offset).toNat = base.toNat+32*index.toNat+offset := by
  have arena := slot_arena base index cap 32 array inside
  have head := slot_number base index cap 32 array inside
  change (byteAddress (slot base index 32) offset).toNat = _
  rw [byteAddress_toNat _ _ (by have upper := arena.upper; omega),head]

/-- Different cells of available nodes cannot alias under source arithmetic. -/
theorem cell_injective (base a b cap : BitVec 64) (x y : Nat)
    (array : AllocatedBytes.Arena base (32*(cap.toNat+1))) (aInside : a.toNat ≤ cap.toNat) (bInside : b.toNat ≤ cap.toNat)
    (xInside : x < 32) (yInside : y < 32) (same : FindLeaf.cell base a x = FindLeaf.cell base b y) : a = b ∧ x = y := by
  have number := congrArg BitVec.toNat same
  rw [cell_number base a cap x array aInside xInside,cell_number base b cap y array bInside yInside] at number
  have indexEq : a.toNat = b.toNat := by omega
  exact ⟨BitVec.eq_of_toNat_eq indexEq,by omega⟩

theorem New.Geometry.cell_after_table {table cap : BitVec 64} (geometry : New.Geometry table cap)
    (node : BitVec 64) (inside : node.toNat ≤ cap.toNat) (offset : Nat) (small : offset < 32) :
    table.toNat+88 ≤ (FindLeaf.cell (New.nodesPointer table cap) node offset).toNat := by
  rw [cell_number _ node cap offset geometry.nodes inside small]
  have beforeKeys := geometry.tableBefore
  have beforeNodes := geometry.keysBefore
  omega

theorem New.Geometry.header_away {table cap : BitVec 64} (geometry : New.Geometry table cap)
    (node : BitVec 64) (inside : node.toNat ≤ cap.toNat) (offset field : Nat) (small : offset < 32) (fieldInside : field < 88) :
    table+BitVec.ofNat 64 field ≠ FindLeaf.cell (New.nodesPointer table cap) node offset := by
  have target := geometry.cell_after_table node inside offset small
  have source := byteAddress_toNat table field (by have bound := geometry.table.upper; omega)
  change (table+BitVec.ofNat 64 field).toNat = table.toNat+field at source
  intro same
  have number := congrArg BitVec.toNat same
  rw [source] at number
  omega

/-- Every real key byte (including its aligned backing word) precedes all
node cells. This protects leaf keys from node-value and link writes. -/
theorem New.Geometry.key_byte_before_node {table cap : BitVec 64} (geometry : New.Geometry table cap)
    (keyNode node : BitVec 64) (keyInside : keyNode.toNat ≤ cap.toNat) (nodeInside : node.toNat ≤ cap.toNat)
    (byte offset : Nat) (byteInside : byte < 32) (offsetInside : offset < 32) :
    (panByteAlignHOL (width:=64) (byteAddress (slot (New.keysPointer table) keyNode 32) byte)).toNat <
      (FindLeaf.cell (New.nodesPointer table cap) node offset).toNat := by
  have keyArena := geometry.key_slot keyNode keyInside
  have keyNumber := slot_number (New.keysPointer table) keyNode cap 32 geometry.keys keyInside
  have byteNumber := byteAddress_toNat (slot (New.keysPointer table) keyNode 32) byte (by have bound := keyArena.upper; omega)
  have aligned := AllocatedBytes.aligned_number (byteAddress (slot (New.keysPointer table) keyNode 32) byte)
  rw [byteNumber,keyNumber] at aligned
  rw [cell_number _ node cap offset geometry.nodes nodeInside offsetInside,aligned]
  have before := geometry.keysBefore
  omega

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.cell_number
#print axioms InitECandidate.Solver.Input.CurrentTable.cell_injective
#print axioms InitECandidate.Solver.Input.CurrentTable.New.Geometry.header_away
#print axioms InitECandidate.Solver.Input.CurrentTable.New.Geometry.key_byte_before_node
