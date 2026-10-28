import InitECandidate.Solver.Input.CurrentTable.NewMemory

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def endPointer (heap cap : BitVec 64) : BitVec 64 := PersistentAlloc.rounded (orderPointer heap cap) (size8 cap)

/-- Current Patricia storage:88metadata bytes, two32-byte-per-slot arrays
and one8-byte-per-slot array, including the reserved zero slot. -/
structure Geometry (heap cap : BitVec 64) : Prop where
  table : AllocatedBytes.Arena heap 88
  keys : AllocatedBytes.Arena (keysPointer heap) (32*(cap.toNat+1))
  nodes : AllocatedBytes.Arena (nodesPointer heap cap) (32*(cap.toNat+1))
  order : AllocatedBytes.Arena (orderPointer heap cap) (8*(cap.toNat+1))
  tableBefore : heap.toNat+88≤(keysPointer heap).toNat
  keysBefore : (keysPointer heap).toNat+32*(cap.toNat+1)≤(nodesPointer heap cap).toNat
  nodesBefore : (nodesPointer heap cap).toNat+32*(cap.toNat+1)≤(orderPointer heap cap).toNat
  orderBefore : (orderPointer heap cap).toNat+8*(cap.toNat+1)≤(endPointer heap cap).toNat
  keysAligned : (keysPointer heap).toNat%8=0
  nodesAligned : (nodesPointer heap cap).toNat%8=0
  orderAligned : (orderPointer heap cap).toNat%8=0
  endAligned : (endPointer heap cap).toNat%8=0
  endBound : (endPointer heap cap).toNat≤2952790016
  bytesBound : heap.toNat+88+72*(cap.toNat+1)≤2952790016
  capacityBound : cap.toNat≤3495251

theorem size_numbers (cap : BitVec 64) (small : cap.toNat≤2^32) :
    (size32 cap).toNat=32*(cap.toNat+1) ∧ (size8 cap).toNat=8*(cap.toNat+1) := by
  have next : (cap+1#64).toNat=cap.toNat+1 := by
    rw [BitVec.toNat_add_of_lt (by change cap.toNat+1<2^64; omega)]
    rfl
  constructor
  · rw [size32,BitVec.toNat_mul,next,Nat.mod_eq_of_lt (by change (cap.toNat+1)*32<2^64; omega)]
    change (cap.toNat+1)*32=32*(cap.toNat+1)
    omega
  · rw [size8,BitVec.toNat_mul,next,Nat.mod_eq_of_lt (by change (cap.toNat+1)*8<2^64; omega)]
    change (cap.toNat+1)*8=8*(cap.toNat+1)
    omega

/-- Only request room derived from the same four actual allocation calls
establishes this physical layout. No ordinary-domain upper bound is used
as a substitute for persistent allocator room. -/
theorem geometry_of_room (heap cap : BitVec 64) (heapLower : 2701131776≤heap.toNat) (small : cap.toNat≤2^32)
    (tableRoom : heap.toNat+88≤2952790016)
    (keysRoom : (keysPointer heap).toNat+(size32 cap).toNat≤2952790016)
    (nodesRoom : (nodesPointer heap cap).toNat+(size32 cap).toNat≤2952790016)
    (orderRoom : (orderPointer heap cap).toNat+(size8 cap).toNat≤2952790016) : Geometry heap cap := by
  have first:=PersistentAlloc.guards heap 88#64 tableRoom
  have second:=PersistentAlloc.guards (keysPointer heap) (size32 cap) keysRoom
  have third:=PersistentAlloc.guards (nodesPointer heap cap) (size32 cap) nodesRoom
  have fourth:=PersistentAlloc.guards (orderPointer heap cap) (size8 cap) orderRoom
  have tableBefore : heap.toNat+88≤(keysPointer heap).toNat := first.2.2.1
  have keysBefore : (keysPointer heap).toNat+(size32 cap).toNat≤(nodesPointer heap cap).toNat := second.2.2.1
  have nodesBefore : (nodesPointer heap cap).toNat+(size32 cap).toNat≤(orderPointer heap cap).toNat := third.2.2.1
  have orderBefore : (orderPointer heap cap).toNat+(size8 cap).toNat≤(endPointer heap cap).toNat := fourth.2.2.1
  obtain ⟨size32Number,size8Number⟩:=size_numbers cap small
  rw [size32Number] at keysBefore nodesBefore keysRoom nodesRoom
  rw [size8Number] at orderBefore orderRoom
  have bytesBound : heap.toNat+88+72*(cap.toNat+1)≤2952790016 := by omega
  exact ⟨⟨heapLower,by omega⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    tableBefore,keysBefore,nodesBefore,orderBefore,first.2.2.2.2,second.2.2.2.2,third.2.2.2.2,fourth.2.2.2.2,fourth.2.2.2.1,
    bytesBound,by omega⟩

/-- The actual power-of-two capacity selected by a normally completed
current database constructor cannot exceed2^21 under the persistent heap
ceiling. Its builder count is consequently at most1048575. -/
theorem power_capacity (heap cap : BitVec 64) (geometry : Geometry heap cap) (bits count : Nat)
    (bitsBound : bits≤32) (capacity : cap=BitVec.ofNat 64 (2^bits)) (sufficient : 2*count+2≤2^bits) :
    bits≤21 ∧ count≤1048575 := by
  have number : cap.toNat=2^bits := by
    rw [capacity,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
  have upper:=geometry.capacityBound
  rw [number] at upper
  have small : bits≤21 := by
    apply Classical.byContradiction
    intro large
    have lower:=Nat.pow_le_pow_right (by decide : 0<2) (show 22≤bits by omega)
    change 4194304≤2^bits at lower
    omega
  have powBound:=Nat.pow_le_pow_right (by decide : 0<2) small
  change 2^bits≤2097152 at powBound
  exact ⟨small,by omega⟩

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.size_numbers
#print axioms InitECandidate.Solver.Input.CurrentTable.New.geometry_of_room
#print axioms InitECandidate.Solver.Input.CurrentTable.New.power_capacity
