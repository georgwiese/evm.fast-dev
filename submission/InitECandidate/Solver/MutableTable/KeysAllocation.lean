import InitECandidate.Solver.MutableTable.KeysAfterOutput
import InitECandidate.Solver.WitnessRadix.AllocationCall

namespace InitECandidate.Solver.MutableTable.Keys
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

def allocationSize (kind : KeyHash.Kind) (count : Nat) : Nat := stride kind * count + 8
def changed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start count paid : Nat) (memory : WordWrites.Memory) :=
  {source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (start + allocationSize kind count))))
    memory := memory
    clock := source.clock - paid}

theorem allocation_multiple (kind : KeyHash.Kind) (count : Nat) : allocationSize kind count % 8 = 0 := by
  simp only [allocationSize, Nat.add_mod, Nat.mul_mod, (stride_bounds kind).2.2, Nat.zero_mul, Nat.zero_mod, Nat.mod_self, Nat.zero_add]

/-- The actual enumerator allocation has no extra rounding slack: its
stride and eight-byte suffix make the requested size already word aligned. -/
theorem allocation_end (kind : KeyHash.Kind) (start count : Nat) (valid : MemoryRegion.Valid (outputRegion kind start count)) :
    PersistentAlloc.rounded (BitVec.ofNat 64 start) (BitVec.ofNat 64 (allocationSize kind count)) = BitVec.ofNat 64 (start + allocationSize kind count) := by
  have upper : start + allocationSize kind count ≤ 33806089496 := valid.upper
  have pointerNat : (BitVec.ofNat 64 start).toNat = start := MemoryRegion.pointer_number _ valid
  have sizeSmall : allocationSize kind count < 2 ^ 64 := by omega
  have amountNat : (BitVec.ofNat 64 (allocationSize kind count)).toNat = allocationSize kind count := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sizeSmall]
  apply BitVec.eq_of_toNat_eq
  rw [PersistentAlloc.rounded_nat _ _ (by rw [pointerNat, amountNat]; omega), pointerNat, amountNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have aligned : start % 8 = 0 := valid.aligned
  have multiple := allocation_multiple kind count
  omega

theorem allocated_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start count : Nat)
    (valid : MemoryRegion.Valid (outputRegion kind start count)) :
    PersistentAlloc.post {source with clock := source.clock - 1} (BitVec.ofNat 64 start) (BitVec.ofNat 64 (allocationSize kind count)) =
      changed source kind start count 1 source.memory := by
  simp only [PersistentAlloc.post, allocation_end kind start count valid, changed]

end InitECandidate.Solver.MutableTable.Keys

#print axioms InitECandidate.Solver.MutableTable.Keys.allocation_multiple
#print axioms InitECandidate.Solver.MutableTable.Keys.allocation_end
#print axioms InitECandidate.Solver.MutableTable.Keys.allocated_state
