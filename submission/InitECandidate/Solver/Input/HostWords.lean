import InitECandidate.Solver.Input.HostLength

namespace InitECandidate.Solver.Input.HostWords
open Flapjack

def dataBytes (input : Guest.InputBlob) (index : Nat) : List UInt8 :=
  (List.range 8).map (fun offset=>Framing.convert ((input[index+offset]?).getD 0))

theorem dataBytes_length (input : Guest.InputBlob) (index : Nat) : (dataBytes input index).length=8 := by simp [dataBytes]

theorem offset_address (index offset : Nat) :
    Guest.inputDataAddr+BitVec.ofNat 64 index+BitVec.ofNat 64 offset=
      Guest.inputDataAddr+BitVec.ofNat 64 (index+offset) := by
  rw [BitVec.add_assoc,BitVec.ofNat_add]

theorem host_byte (input : Guest.InputBlob) (index offset : Nat) (visible : index+offset<Guest.maxInputBytes) :
    Guest.guestHostMemory input (Guest.inputDataAddr+BitVec.ofNat 64 index+BitVec.ofNat 64 offset)=
      some (Framing.convert ((input[index+offset]?).getD 0)) := by
  rw [offset_address]
  exact Framing.host_data input (index+offset) visible

theorem bytes (input : Guest.InputBlob) (index : Nat) (visible : index+8≤Guest.maxInputBytes) :
    SharedRead.bytes (Guest.guestHostMemory input) (Guest.inputDataAddr+BitVec.ofNat 64 index)=dataBytes input index := by
  apply List.map_congr_left
  intro offset member
  have inside:=List.mem_range.mp member
  rw [host_byte input index offset (by omega)]
  rfl

theorem present (input : Guest.InputBlob) (index : Nat) (visible : index+8≤Guest.maxInputBytes) :
    ∀ offset<8,(Guest.guestHostMemory input (Guest.inputDataAddr+BitVec.ofNat 64 index+BitVec.ofNat 64 offset)).isSome=true := by
  intro offset inside
  rw [host_byte input index offset (by omega)]
  rfl

/-- A word beginning at any copy-loop index fits the host arena, including the
last partially populated word. The arena's capacity is a multiple of eight. -/
theorem final_word_visible (length index : Nat) (bounded : length≤Guest.maxInputBytes)
    (inside : index<length) (aligned : index%8=0) : index+8≤Guest.maxInputBytes := by
  change length≤134217712 at bounded
  change index+8≤134217712
  omega

end InitECandidate.Solver.Input.HostWords

#print axioms InitECandidate.Solver.Input.HostWords.dataBytes_length
#print axioms InitECandidate.Solver.Input.HostWords.offset_address
#print axioms InitECandidate.Solver.Input.HostWords.host_byte
#print axioms InitECandidate.Solver.Input.HostWords.bytes
#print axioms InitECandidate.Solver.Input.HostWords.present
#print axioms InitECandidate.Solver.Input.HostWords.final_word_visible
