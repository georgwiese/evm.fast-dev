import InitECandidate.Solver.Input.HostWords
import InitECandidate.Solver.WitnessRadix.AllocationDomain

namespace InitECandidate.Solver.Input.Blob
open Flapjack

theorem data_address_number (index : Nat) (visible : index<Guest.maxInputBytes) :
    (Guest.inputDataAddr+BitVec.ofNat 64 index).toNat=1073741840+index := by
  change index<134217712 at visible
  have small : index<2^64 := by omega
  have encoded : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  rw [BitVec.toNat_add_of_lt (by change 1073741840+(BitVec.ofNat 64 index).toNat<2^64; rw [encoded]; omega),encoded]
  rfl

theorem data_mapped (index : Nat) (visible : index<Guest.maxInputBytes) (aligned : index%8=0) :
    InitE.sharedDomain (Guest.inputDataAddr+BitVec.ofNat 64 index) := by
  have number:=data_address_number index visible
  refine ⟨?_,Or.inl ?_⟩
  · change holAligned (holLOG2 8) _=true
    rw [holLOG2_eq_log2 (by decide)]
    rw [holAligned_iff,number]
    change (1073741840+index)%8=0
    omega
  · change 1073741824≤(Guest.inputDataAddr+BitVec.ofNat 64 index).toNat ∧
      (Guest.inputDataAddr+BitVec.ofNat 64 index).toNat<1207959552
    rw [number]
    change index<134217712 at visible
    omega

/-- Ordinary heap words touched by the real input loop are mapped from one
natural allocation extent; this does not assume their initial contents. -/
theorem heap_copy_mapped (pointer : BitVec 64) (length index : Nat)
    (lower : 2701131776≤pointer.toNat) (upper : pointer.toNat+length+8≤33806089496)
    (aligned : pointer.toNat%8=0) (inside : index<length) (indexAligned : index%8=0) :
    InitE.ordinaryDomain (pointer+BitVec.ofNat 64 index) := by
  have encoded : (BitVec.ofNat 64 index).toNat=index := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have number : (pointer+BitVec.ofNat 64 index).toNat=pointer.toNat+index := by
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega),encoded]
  apply WitnessRadix.BackingLayout.ordinary_mapped
  · rw [number]; omega
  · rw [number]; omega
  · rw [number]; omega

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.data_address_number
#print axioms InitECandidate.Solver.Input.Blob.data_mapped
#print axioms InitECandidate.Solver.Input.Blob.heap_copy_mapped
