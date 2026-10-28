import InitECandidate.Solver.Input.CurrentTable.NewGeometry

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The actual current slot expression, with a source-word node index. -/
def slot (base index : BitVec 64) (width : Nat) : BitVec 64 :=
  base+index*BitVec.ofNat 64 width

theorem slot_address (base index : BitVec 64) (width : Nat) :
    slot base index width = byteAddress base (width*index.toNat) := by
  simp [slot,byteAddress,BitVec.ofNat_mul,BitVec.mul_comm]

/-- Constructor-derived full array room maps every available real slot,
including the reserved zero slot; it does not initialize any contents. -/
theorem slot_arena (base index cap : BitVec 64) (width : Nat)
    (array : AllocatedBytes.Arena base (width*(cap.toNat+1))) (inside : index.toNat ≤ cap.toNat) :
    AllocatedBytes.Arena (slot base index width) width := by
  rw [slot_address]
  apply AllocatedBytes.Arena.subrange base (width*(cap.toNat+1)) (width*index.toNat) width array
  simpa only [Nat.mul_succ,Nat.mul_add,Nat.mul_one] using Nat.mul_le_mul_left width (Nat.succ_le_succ inside)

theorem New.Geometry.node_slot {table cap : BitVec 64} (geometry : New.Geometry table cap)
    (index : BitVec 64) (inside : index.toNat ≤ cap.toNat) :
    AllocatedBytes.Arena (slot (New.nodesPointer table cap) index 32) 32 :=
  slot_arena _ index cap 32 geometry.nodes inside

theorem New.Geometry.key_slot {table cap : BitVec 64} (geometry : New.Geometry table cap)
    (index : BitVec 64) (inside : index.toNat ≤ cap.toNat) :
    AllocatedBytes.Arena (slot (New.keysPointer table) index 32) 32 :=
  slot_arena _ index cap 32 geometry.keys inside

theorem New.Geometry.order_slot {table cap : BitVec 64} (geometry : New.Geometry table cap)
    (index : BitVec 64) (inside : index.toNat ≤ cap.toNat) :
    AllocatedBytes.Arena (slot (New.orderPointer table cap) index 8) 8 :=
  slot_arena _ index cap 8 geometry.order inside

theorem slot_aligned (base index cap : BitVec 64) (width : Nat)
    (array : AllocatedBytes.Arena base (width*(cap.toNat+1))) (inside : index.toNat ≤ cap.toNat)
    (baseAligned : base.toNat%8 = 0) (widthAligned : width%8 = 0) :
    (slot base index width).toNat%8 = 0 := by
  rw [slot_address]
  apply byteAddress_aligned base (width*index.toNat) baseAligned
  · simp [Nat.mul_mod,widthAligned]
  · have extent : width*index.toNat ≤ width*(cap.toNat+1) :=
      Nat.mul_le_mul_left width (by omega)
    have upper := array.upper
    omega

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.slot_arena
#print axioms InitECandidate.Solver.Input.CurrentTable.New.Geometry.node_slot
#print axioms InitECandidate.Solver.Input.CurrentTable.New.Geometry.key_slot
#print axioms InitECandidate.Solver.Input.CurrentTable.New.Geometry.order_slot
#print axioms InitECandidate.Solver.Input.CurrentTable.slot_aligned
