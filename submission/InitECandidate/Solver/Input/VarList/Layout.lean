import InitECandidate.Solver.Input.VarList.OffsetRead

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

/-- Natural geometry of the real decoded slice and its fresh record allocation.
The whole-function connection must establish these premises at allocation. -/
structure Plan (input : Guest.InputBlob) where
  inputPointer : BitVec 64
  array : BitVec 64
  start : Nat
  length : Nat
  count : Nat
  positive : 0<count
  header : 4*count≤length
  slice : start+length≤input.length%2^64
  inputLower : 2701131776≤inputPointer.toNat
  inputAligned : inputPointer.toNat%8=0
  arrayAligned : array.toNat%8=0
  arrayAfter : inputPointer.toNat+input.length%2^64+8≤array.toNat
  arrayRoom : array.toNat+16*count≤33806089496

def row (array : BitVec 64) (index : Nat) : BitVec 64 := array+BitVec.ofNat 64 (16*index)
def lengthCell (array : BitVec 64) (index : Nat) : BitVec 64 := row array index+8#64

theorem Plan.count_small {input : Guest.InputBlob} (plan : Plan input) : plan.count<2^31 := by
  have h:=plan.arrayRoom
  omega

theorem Plan.input_fits {input : Guest.InputBlob} (plan : Plan input) :
    plan.inputPointer.toNat+input.length%2^64<2^64 := by
  have after:=plan.arrayAfter
  have room:=plan.arrayRoom
  omega

theorem Plan.offset_inside {input : Guest.InputBlob} (plan : Plan input) (index : Nat) (small : index<plan.count) :
    plan.start+4*index+4≤input.length%2^64 := by
  have h:=plan.header
  have s:=plan.slice
  omega

theorem Plan.row_nat {input : Guest.InputBlob} (plan : Plan input) (index : Nat) (small : index<plan.count) :
    (row plan.array index).toNat=plan.array.toNat+16*index := by
  have room:=plan.arrayRoom
  have encoded : (BitVec.ofNat 64 (16*index)).toNat=16*index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [row,BitVec.toNat_add_of_lt (by rw [encoded]; omega),encoded]

theorem Plan.length_nat {input : Guest.InputBlob} (plan : Plan input) (index : Nat) (small : index<plan.count) :
    (lengthCell plan.array index).toNat=plan.array.toNat+16*index+8 := by
  have room:=plan.arrayRoom
  have first:=plan.row_nat index small
  rw [lengthCell,BitVec.toNat_add_of_lt (by change (row plan.array index).toNat+8<2^64; rw [first]; omega),first]
  rfl

theorem Plan.row_mapped {input : Guest.InputBlob} (plan : Plan input) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (domain : source.memaddrs=InitE.ordinaryDomain) (index : Nat) (small : index<plan.count) :
    source.memaddrs (row plan.array index) := by
  rw [domain]
  have number:=plan.row_nat index small
  have after:=plan.arrayAfter
  have lower:=plan.inputLower
  have room:=plan.arrayRoom
  have aligned:=plan.arrayAligned
  apply WitnessRadix.BackingLayout.ordinary_mapped
  · rw [number]; omega
  · rw [number]; omega
  · rw [number]; omega

theorem Plan.length_mapped {input : Guest.InputBlob} (plan : Plan input) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (domain : source.memaddrs=InitE.ordinaryDomain) (index : Nat) (small : index<plan.count) :
    source.memaddrs (lengthCell plan.array index) := by
  rw [domain]
  have number:=plan.length_nat index small
  have after:=plan.arrayAfter
  have lower:=plan.inputLower
  have room:=plan.arrayRoom
  have aligned:=plan.arrayAligned
  apply WitnessRadix.BackingLayout.ordinary_mapped
  · rw [number]; omega
  · rw [number]; omega
  · rw [number]; omega

theorem Plan.row_store_input {input : Guest.InputBlob} (plan : Plan input) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : Blob.HeapInput source input plan.inputPointer) (index : Nat) (small : index<plan.count) (value : BitVec 64) :
    Blob.HeapInput {source with memory:=WitnessRadix.StoreWord.put source.memory (row plan.array index) value} input plan.inputPointer := by
  apply Blob.HeapInput.store_separate source input plan.inputPointer (row plan.array index) value heap plan.inputAligned plan.input_fits
  right
  rw [plan.row_nat index small]
  have h:=plan.arrayAfter
  omega

theorem Plan.length_store_input {input : Guest.InputBlob} (plan : Plan input) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : Blob.HeapInput source input plan.inputPointer) (index : Nat) (small : index<plan.count) (value : BitVec 64) :
    Blob.HeapInput {source with memory:=WitnessRadix.StoreWord.put source.memory (lengthCell plan.array index) value} input plan.inputPointer := by
  apply Blob.HeapInput.store_separate source input plan.inputPointer (lengthCell plan.array index) value heap plan.inputAligned plan.input_fits
  right
  rw [plan.length_nat index small]
  have h:=plan.arrayAfter
  omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Plan.count_small
#print axioms InitECandidate.Solver.Input.VarList.Plan.input_fits
#print axioms InitECandidate.Solver.Input.VarList.Plan.offset_inside
#print axioms InitECandidate.Solver.Input.VarList.Plan.row_nat
#print axioms InitECandidate.Solver.Input.VarList.Plan.length_nat
#print axioms InitECandidate.Solver.Input.VarList.Plan.row_mapped
#print axioms InitECandidate.Solver.Input.VarList.Plan.length_mapped
#print axioms InitECandidate.Solver.Input.VarList.Plan.row_store_input
#print axioms InitECandidate.Solver.Input.VarList.Plan.length_store_input
