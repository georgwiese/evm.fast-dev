import InitECandidate.Solver.WitnessRadix.Addressing
import InitECandidate.Solver.WitnessRadix.MemoryBytes

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack

inductive Pool where
  | header | keys | vals | primary | backup | records
  deriving DecidableEq

structure Layout where
  table : BitVec 64
  keys : BitVec 64
  vals : BitVec 64
  primary : BitVec 64
  backup : BitVec 64
  records : BitVec 64
  count : Nat
  capacity : Nat

def base (layout : Layout) : Pool → BitVec 64
  | .header => layout.table
  | .keys => layout.keys
  | .vals => layout.vals
  | .primary => layout.primary
  | .backup => layout.backup
  | .records => layout.records

def size (layout : Layout) : Pool → Nat
  | .header => 72
  | .keys => 32 * layout.capacity
  | .vals | .primary | .backup => 8 * layout.capacity
  | .records => 16 * layout.count

def cell (layout : Layout) (pool : Pool) (offset : Nat) : BitVec 64 := byteAddress (base layout pool) offset

/-- Actual allocated extents, with no integer wrap and separate backing pools.
The allocator/constructor must establish this entry invariant. -/
structure Valid (layout : Layout) : Prop where
  room : 2 * layout.count + 2 ≤ layout.capacity
  noWrap : ∀ pool, (base layout pool).toNat + size layout pool < 2 ^ 64
  aligned : ∀ pool, (base layout pool).toNat % 8 = 0
  positive : ∀ pool, 0 < (base layout pool).toNat
  separate : ∀ left right, left ≠ right → ∀ offset < size layout left, ∀ other < size layout right,
    cell layout left offset ≠ cell layout right other

theorem count_small (layout : Layout) (valid : Valid layout) : layout.count < 2 ^ 63 := by
  have bound := valid.noWrap .records
  change layout.records.toNat + 16 * layout.count < 2 ^ 64 at bound
  omega

theorem cell_injective (layout : Layout) (valid : Valid layout) (pool : Pool) (left right : Nat)
    (leftBound : left < size layout pool) (rightBound : right < size layout pool) (different : left ≠ right) :
    cell layout pool left ≠ cell layout pool right := by
  exact byteAddress_ne _ _ _ (by have := valid.noWrap pool; omega)
    (by have := valid.noWrap pool; omega) different

theorem hash_head (layout : Layout) (ordinal : Nat) :
    layout.keys + BitVec.ofNat 64 ordinal * 32#64 = cell layout .keys (32 * ordinal) := by
  change layout.keys + BitVec.ofNat 64 ordinal * BitVec.ofNat 64 32 = layout.keys + BitVec.ofNat 64 (32 * ordinal)
  rw [Nat.mul_comm 32 ordinal, BitVec.ofNat_mul]

theorem hash_fits (layout : Layout) (valid : Valid layout) (ordinal : Nat) (inside : ordinal < layout.count) :
    (layout.keys + BitVec.ofNat 64 ordinal * 32#64).toNat + 32 < 2 ^ 64 := by
  have allocation : layout.keys.toNat + 32 * layout.capacity < 2 ^ 64 := valid.noWrap .keys
  have room := valid.room
  rw [hash_head]
  change (byteAddress layout.keys (32 * ordinal)).toNat + 32 < 2 ^ 64
  rw [byteAddress_toNat _ _ (by omega)]
  omega

/-- Alignment converts every byte of any valid hash ordinal to one of its
four protected key words. -/
theorem hash_byte_cell (layout : Layout) (valid : Valid layout) (ordinal : Nat) (inside : ordinal < layout.count)
    (byte : Fin 32) :
    panByteAlignHOL (width := 64)
      (layout.keys + BitVec.ofNat 64 ordinal * 32#64 + BitVec.ofNat 64 byte.val) =
      cell layout .keys (32 * ordinal + 8 * (byte.val / 8)) := by
  have allocation : layout.keys.toNat + 32 * layout.capacity < 2 ^ 64 := valid.noWrap .keys
  have room := valid.room
  have aligned : (layout.keys + BitVec.ofNat 64 ordinal * 32#64).toNat % 8 = 0 := by
    rw [hash_head]
    exact byteAddress_aligned layout.keys (32 * ordinal) (valid.aligned .keys) (by omega) (by omega)
  rw [MemoryBytes.aligned_offset _ _ byte.isLt aligned (hash_fits layout valid ordinal inside), hash_head]
  simp only [cell, base, byteAddress, BitVec.ofNat_add, BitVec.add_assoc]

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.count_small
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.hash_byte_cell
