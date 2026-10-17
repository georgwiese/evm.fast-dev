import InitECandidate.Solver.Input.VarList.FirstChecks

namespace InitECandidate.Solver.Input.VarList

theorem count_encode (input : Guest.InputBlob) (start : Nat) :
    countWord (BitVec.ofNat 64 (Guest.GasLimit.le32 input start))=BitVec.ofNat 64 (Guest.GasLimit.le32 input start/4) := by
  apply BitVec.eq_of_toNat_eq
  rw [count_number,RawScalar.le32_number,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=RawScalar.le32_lt input start; omega)]

theorem count_size (input : Guest.InputBlob) (start : Nat) : Guest.GasLimit.le32 input start/4<2^30 := by
  have bound:=RawScalar.le32_lt input start
  omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.count_encode
#print axioms InitECandidate.Solver.Input.VarList.count_size
