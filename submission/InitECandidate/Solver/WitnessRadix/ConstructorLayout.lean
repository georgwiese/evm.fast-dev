import InitECandidate.Solver.WitnessRadix.ConstructorCopy
import InitECandidate.Solver.WitnessRadix.LayoutCells
import InitECandidate.Solver.WitnessRadix.LayoutOwnership

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

def writeAddresses (index : Nat) : List Address :=
  [(.keys, 32 * index), (.keys, 32 * index + 8), (.keys, 32 * index + 16),
   (.keys, 32 * index + 24), (.vals, 8 * index), (.primary, 8 * index)]

def writes (layout : Layout) (index : Nat) (words : Fin 4 → BitVec 64) :
    List (BitVec 64 × BitVec 64) :=
  Copy32.writes (layout.keys + BitVec.ofNat 64 index * 32#64) words ++
    recordWrites layout.vals layout.primary layout.records (BitVec.ofNat 64 index)

theorem hash_limb_cell (layout : Layout) (index limb : Nat) :
    layout.keys + BitVec.ofNat 64 index * 32#64 + BitVec.ofNat 64 (8 * limb) =
      cell layout .keys (32 * index + 8 * limb) := by
  rw [hash_head]
  simp only [cell, base, byteAddress, BitVec.ofNat_add, BitVec.add_assoc]

theorem primary_cell (layout : Layout) (index : Nat) :
    layout.primary + BitVec.ofNat 64 index * 8#64 = cell layout .primary (8 * index) := by
  change layout.primary + BitVec.ofNat 64 index * BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm index 8]
  rfl

theorem record_cell (layout : Layout) (index : Nat) :
    layout.records + BitVec.ofNat 64 index * 16#64 = record layout index := by
  change layout.records + BitVec.ofNat 64 index * BitVec.ofNat 64 16 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm index 16]
  rfl

theorem write_cells (layout : Layout) (index : Nat) (words : Fin 4 → BitVec 64) :
    (writes layout index words).map Prod.fst = (writeAddresses index).map (address layout) := by
  simp only [writes, Copy32.writes, recordWrites, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, Prod.fst]
  rw [hash_head, vals_cell, primary_cell]
  simp only [writeAddresses, List.map_cons, List.map_nil, address, cell, base, byteAddress,
    BitVec.ofNat_add, BitVec.add_assoc]

theorem write_bounds (layout : Layout) (valid : Valid layout) (index : Nat) (inside : index < layout.count) :
    ∀ entry ∈ writeAddresses index, entry.2 + 8 ≤ size layout entry.1 := by
  have room := valid.room
  intro entry member
  simp only [writeAddresses, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [size] <;> omega

theorem writes_distinct (layout : Layout) (valid : Valid layout) (index : Nat)
    (inside : index < layout.count) (words : Fin 4 → BitVec 64) :
    ((writes layout index words).map Prod.fst).Nodup := by
  rw [write_cells]
  apply addresses_nodup layout valid
  · intro entry member
    have bound := write_bounds layout valid index inside entry member
    omega
  · simp [writeAddresses, List.nodup_cons]

theorem writes_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout) (index : Nat) (inside : index < layout.count) :
    ∀ entry ∈ writeAddresses index, source.memaddrs (address layout entry) := by
  intro entry member
  apply mapped entry.1 entry.2
  · simp only [writeAddresses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  · exact write_bounds layout valid index inside entry member

theorem hash_aligned (layout : Layout) (valid : Valid layout) (index : Nat) (inside : index < layout.count) :
    (layout.keys + BitVec.ofNat 64 index * 32#64).toNat % 8 = 0 := by
  rw [hash_head]
  change (byteAddress layout.keys (32 * index)).toNat % 8 = 0
  exact byteAddress_aligned _ _ (valid.aligned .keys) (by omega) (by
    have bound := valid.noWrap .keys; have room := valid.room
    change layout.keys.toNat + 32 * layout.capacity < 2 ^ 64 at bound
    omega)

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.write_cells
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.writes_distinct
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.writes_mapped
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.hash_aligned
