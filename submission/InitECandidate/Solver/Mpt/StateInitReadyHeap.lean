import InitECandidate.Solver.Mpt.StateInitPrefixFields

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Actual40-byte workspace room and the current alignment determine the
next heap exactly, retaining ordinary bounded/aligned frontier geometry. -/
theorem workspace_heap_geometry (heap : BitVec 64) (arena : AllocatedBytes.Arena heap 40) (aligned : heap.toNat%8=0) :
    AllocatedBytes.Arena (PersistentAlloc.rounded heap 40#64) 0 ∧
      (PersistentAlloc.rounded heap 40#64).toNat%8=0 ∧ heap.toNat≤(PersistentAlloc.rounded heap 40#64).toNat := by
  have raw:=PersistentAlloc.rounded_nat heap 40#64 (by have h:=arena.upper; change heap.toNat+40+7<2^64; omega)
  have number : (PersistentAlloc.rounded heap 40#64).toNat=heap.toNat+40 := by
    rw [raw]
    change (heap.toNat+40+7)/8*8=heap.toNat+40
    omega
  rw [number]
  exact ⟨⟨by have h:=arena.lower; omega,by have h:=arena.upper; omega⟩,by omega,by omega⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.workspace_heap_geometry
