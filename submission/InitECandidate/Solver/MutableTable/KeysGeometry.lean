import InitECandidate.Solver.MutableTable.KeysProgram
import InitECandidate.Solver.MutableTable.MemoryModelPoolFrame

namespace InitECandidate.Solver.MutableTable.Keys
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

def outputRegion (kind : KeyHash.Kind) (start count : Nat) : MemoryRegion.Region := ⟨start, stride kind * count + 8⟩
def keyRegion (kind : KeyHash.Kind) (plan : Plan) (slot : Nat) : MemoryRegion.Region := ⟨plan.base .keys + stride kind * slot, stride kind⟩
def destinationRegion (kind : KeyHash.Kind) (start index : Nat) : MemoryRegion.Region := ⟨start + stride kind * index, stride kind⟩

theorem scaled_pointer (base step index : Nat) :
    BitVec.ofNat 64 base + BitVec.ofNat 64 index * BitVec.ofNat 64 step = BitVec.ofNat 64 (base + step * index) := by
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm index step]

theorem key_region_valid (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (slot : Nat) (inside : slot < plan.capacity) :
    MemoryRegion.Valid (keyRegion kind plan slot) := by
  have full : stride kind * slot + stride kind ≤ stride kind * plan.capacity := by
    have bound := Nat.mul_le_mul_left (stride kind) (Nat.succ_le_of_lt inside)
    simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] using bound
  exact MemoryRegion.slice_valid ⟨plan.base .keys, size kind plan .keys⟩ (MemoryRegion.pool_valid kind plan valid .keys) _ _ full
    (by simp only [Nat.mul_mod, (stride_bounds kind).2.2, Nat.zero_mul, Nat.zero_mod])

theorem destination_region_valid (kind : KeyHash.Kind) (start count index : Nat) (valid : MemoryRegion.Valid (outputRegion kind start count))
    (inside : index < count) : MemoryRegion.Valid (destinationRegion kind start index) := by
  have full : stride kind * index + stride kind ≤ stride kind * count := by
    have bound := Nat.mul_le_mul_left (stride kind) (Nat.succ_le_of_lt inside)
    simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] using bound
  exact MemoryRegion.slice_valid (outputRegion kind start count) valid _ _ (by change stride kind * index + stride kind ≤ stride kind * count + 8; omega)
    (by simp only [Nat.mul_mod, (stride_bounds kind).2.2, Nat.zero_mul, Nat.zero_mod])

/-- A copied padded key has the constructor's full stride, including bytes
beyond the logical key width. Both real source and destination are owned. -/
theorem copy_regions (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (start count index slot : Nat)
    (outValid : MemoryRegion.Valid (outputRegion kind start count)) (indexInside : index < count) (slotInside : slot < plan.capacity) :
    CopyContext.Mapped source (MemoryRegion.pointer (keyRegion kind plan slot)) (MemoryRegion.pointer (destinationRegion kind start index)) (stride kind) :=
  MemoryRegion.copy_mapped source domain _ _ (key_region_valid kind plan valid slot slotInside) (destination_region_valid kind start count index outValid indexInside) _ (Nat.le_refl _) (Nat.le_refl _)

theorem copy_preserves_table (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (start count index slot : Nat) (outValid : MemoryRegion.Valid (outputRegion kind start count)) (indexInside : index < count)
    (earlier : ∀ pool, plan.base pool + size kind plan pool ≤ start) :
    MemoryModel.PoolFrame source.memory
      (CopyGeneral.resultMemory source.memory source.be (MemoryRegion.pointer (keyRegion kind plan slot)) (MemoryRegion.pointer (destinationRegion kind start index)) (stride kind)) kind plan := by
  intro pool offset inside
  apply CopyGeneral.resultMemory_away
  apply MemoryRegion.copy_away (destinationRegion kind start index) (destination_region_valid kind start count index outValid indexInside) _ (Nat.le_refl _)
  left
  rw [number kind plan valid pool offset inside]
  change plan.base pool + offset < start + stride kind * index
  have bound := earlier pool
  omega

end InitECandidate.Solver.MutableTable.Keys

#print axioms InitECandidate.Solver.MutableTable.Keys.scaled_pointer
#print axioms InitECandidate.Solver.MutableTable.Keys.key_region_valid
#print axioms InitECandidate.Solver.MutableTable.Keys.destination_region_valid
#print axioms InitECandidate.Solver.MutableTable.Keys.copy_regions
#print axioms InitECandidate.Solver.MutableTable.Keys.copy_preserves_table
