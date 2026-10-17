import InitECandidate.Solver.MutableTable.LayoutWrites32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem word_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pool : Pool) (offset : Nat) (inside : offset<size plan pool) (aligned : offset%8=0) :
    source.memaddrs (cell plan pool offset) := by
  have fits:=ready.fits
  have room:=ready.room
  have lower:=ready.recordsLower
  have before:=ready.recordsBefore
  have baseAligned:=base_aligned plan ready pool
  rw [domain]
  apply BackingLayout.ordinary_mapped _ (by rw [number plan ready pool offset inside];have:=bounds plan ready pool;omega) ?_ ?_
  · rw [number plan ready pool offset inside]
    cases pool <;> simp only [base,size] at inside ⊢ <;> omega
  · rw [number plan ready pool offset inside]
    omega

theorem key_aligned (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (key : BitVec 64)
    (index : Nat) (inside : index<plan.capacity) :
    ((parameters plan key).keys+BitVec.ofNat 64 index*(parameters plan key).stride).toNat%8=0 := by
  have number:=number plan ready .keys (32*index) (by change _<32*plan.capacity;omega)
  have address:=key_cell plan key index 0
  simp only [Nat.add_zero,BitVec.add_zero] at address
  rw [address,number]
  have aligned:=base_aligned plan ready .keys
  omega

theorem key_fits (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (key : BitVec 64)
    (index : Nat) (inside : index<plan.capacity) :
    ((parameters plan key).keys+BitVec.ofNat 64 index*(parameters plan key).stride).toNat+32<2^64 := by
  have fits:=ready.fits
  have number:=number plan ready .keys (32*index) (by change _<32*plan.capacity;omega)
  have address:=key_cell plan key index 0
  simp only [Nat.add_zero,BitVec.add_zero] at address
  rw [address,number]
  simp only [base]
  omega

theorem values_fit (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) :
    (BitVec.ofNat 64 (base plan .values)).toNat+8*plan.capacity<2^64 := by
  have fits:=ready.fits
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by simp only [base];omega)]
  simp only [base]
  omega

theorem key_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (key : BitVec 64) (index : Nat) (inside : index<plan.capacity) (limb : Fin 4) :
    source.memaddrs ((parameters plan key).keys+BitVec.ofNat 64 index*(parameters plan key).stride+BitVec.ofNat 64 (8*limb.val)) := by
  rw [key_cell]
  exact word_mapped source plan ready domain .keys _ (by change _<32*plan.capacity;have:=limb.isLt;omega) (by omega)

theorem used_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (key : BitVec 64) (index : Nat) (inside : index<plan.capacity) :
    source.memaddrs (panByteAlignHOL (width:=64) ((parameters plan key).used+BitVec.ofNat 64 index)) := by
  rw [used_byte_cell plan ready key index inside]
  exact word_mapped source plan ready domain .used _ (by change _<plan.capacity;omega) (by omega)

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.word_mapped
#print axioms InitECandidate.Solver.MutableTable.Layout32.key_fits
#print axioms InitECandidate.Solver.MutableTable.Layout32.key_mapped
#print axioms InitECandidate.Solver.MutableTable.Layout32.used_mapped
