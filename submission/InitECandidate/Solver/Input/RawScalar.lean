import InitECandidate.Solver.Input.HeapFlatScalar

namespace InitECandidate.Solver.Input.RawScalar

theorem byte_lt (input : Guest.InputBlob) (index : Nat) : Guest.GasLimit.byte input index<256 :=
  ((input[index]?).getD 0).isLt

/-- Raw scalar bounds at every mathematical input index, without a host-window
or input-size premise. Out-of-list reads are the specified zero bytes. -/
theorem le32_lt (input : Guest.InputBlob) (index : Nat) : Guest.GasLimit.le32 input index<2^32 := by
  have h0:=byte_lt input index
  have h1:=byte_lt input (index+1)
  have h2:=byte_lt input (index+2)
  have h3:=byte_lt input (index+3)
  unfold Guest.GasLimit.le32
  omega

theorem le64_lt (input : Guest.InputBlob) (index : Nat) : Guest.GasLimit.le64 input index<2^64 := by
  have first:=le32_lt input index
  have second:=le32_lt input (index+4)
  unfold Guest.GasLimit.le64
  omega

theorem le32_number (input : Guest.InputBlob) (index : Nat) :
    (BitVec.ofNat 64 (Guest.GasLimit.le32 input index)).toNat=Guest.GasLimit.le32 input index := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=le32_lt input index; omega)]

theorem le64_number (input : Guest.InputBlob) (index : Nat) :
    (BitVec.ofNat 64 (Guest.GasLimit.le64 input index)).toNat=Guest.GasLimit.le64 input index := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (le64_lt input index)]

end InitECandidate.Solver.Input.RawScalar

#print axioms InitECandidate.Solver.Input.RawScalar.byte_lt
#print axioms InitECandidate.Solver.Input.RawScalar.le32_lt
#print axioms InitECandidate.Solver.Input.RawScalar.le64_lt
#print axioms InitECandidate.Solver.Input.RawScalar.le32_number
#print axioms InitECandidate.Solver.Input.RawScalar.le64_number
