import InitECandidate.Solver.Input.SharedReadExecution

namespace InitECandidate.Solver.Input.HostLength
open Flapjack

theorem framed_byte (input : Guest.InputBlob) (index : Nat) (inside : index<8) :
    ((Guest.hostInputBytes input)[8+index]?).getD 0=((Guest.leBytes (BitVec.ofNat 64 input.length))[index]?).getD 0 := by
  let data := input.map (fun byte => UInt8.ofNat byte.toNat)++List.replicate ((8-input.length%8)%8) 0
  have grouped : Guest.hostInputBytes input=List.replicate 8 0++(Guest.leBytes (BitVec.ofNat 64 input.length)++data) := by
    simp [Guest.hostInputBytes,data,List.append_assoc]
  rw [grouped,List.getElem?_append_right (by simp)]
  simp only [List.length_replicate,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa [Guest.leBytes] using inside)]

theorem host_byte (input : Guest.InputBlob) (index : Nat) (inside : index<8) :
    Guest.guestHostMemory input (Guest.inputLenAddr+BitVec.ofNat 64 index)=
      some (((Guest.leBytes (BitVec.ofNat 64 input.length))[index]?).getD 0) := by
  have encoded : (BitVec.ofNat 64 index).toNat=index := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have addressNat : (Guest.inputLenAddr+BitVec.ofNat 64 index).toNat=1073741832+index := by
    rw [BitVec.toNat_add_of_lt (by
      change 1073741832+(BitVec.ofNat 64 index).toNat<2^64
      rw [encoded]; omega),encoded]
    rfl
  have inArena : Guest.inputAddr≤Guest.inputLenAddr+BitVec.ofNat 64 index ∧
      Guest.inputLenAddr+BitVec.ofNat 64 index<Guest.inputAddr+Guest.inputArenaSize := by
    change 1073741824≤(Guest.inputLenAddr+BitVec.ofNat 64 index).toNat ∧
      (Guest.inputLenAddr+BitVec.ofNat 64 index).toNat<1207959552
    rw [addressNat]
    omega
  have offset : (Guest.inputLenAddr+BitVec.ofNat 64 index-Guest.inputAddr).toNat=8+index := by
    rw [BitVec.toNat_sub_of_le inArena.1,addressNat]
    change 1073741832+index-1073741824=8+index
    omega
  simp only [Guest.guestHostMemory,inArena,and_self,↓reduceIte,offset,framed_byte input index inside]

theorem bytes (input : Guest.InputBlob) : SharedRead.bytes (Guest.guestHostMemory input) Guest.inputLenAddr=Guest.leBytes (BitVec.ofNat 64 input.length) := by
  apply List.ext_getElem
  · simp [SharedRead.bytes,Guest.leBytes]
  · intro index left right
    have inside : index<8 := by simpa [SharedRead.bytes] using left
    simp only [SharedRead.bytes,List.getElem_map,List.getElem_range]
    rw [host_byte input index inside]
    rw [List.getElem?_eq_getElem right]
    rfl

theorem present (input : Guest.InputBlob) : ∀ offset<8,(Guest.guestHostMemory input (Guest.inputLenAddr+BitVec.ofNat 64 offset)).isSome=true := by
  intro offset inside
  rw [host_byte input offset inside]
  rfl

end InitECandidate.Solver.Input.HostLength

#print axioms InitECandidate.Solver.Input.HostLength.framed_byte
#print axioms InitECandidate.Solver.Input.HostLength.host_byte
#print axioms InitECandidate.Solver.Input.HostLength.bytes
#print axioms InitECandidate.Solver.Input.HostLength.present
