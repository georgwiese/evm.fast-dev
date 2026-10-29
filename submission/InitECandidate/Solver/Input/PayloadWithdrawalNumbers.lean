import InitECandidate.Solver.Input.PayloadPrefixProgram
import InitECandidate.Solver.Input.OffsetsAnyLoop
import InitECandidate.Solver.Input.RawScalar

namespace InitECandidate.Solver.Input.Payload
open Flapjack PanSemStateFiniteExact

def withdrawalCount (input : Guest.InputBlob) : Nat := (Guest.GasLimit.le32 input 590-Guest.GasLimit.le32 input 570)/44

theorem withdrawal_difference (input : Guest.InputBlob) (length : BitVec 64)
    (valid : ∀ position<4,Offsets.ValidAt 540#64 length (offsetWords input) position) :
    Guest.GasLimit.le32 input 570≤Guest.GasLimit.le32 input 590 ∧
      (offsetWords input 3-offsetWords input 2).toNat=Guest.GasLimit.le32 input 590-Guest.GasLimit.le32 input 570 ∧
      Guest.GasLimit.le32 input 590-Guest.GasLimit.le32 input 570≤length.toNat := by
  have last:=valid 3 (by decide)
  have previous : (offsetWords input 2).toNat≤(offsetWords input 3).toNat:=last.2.2 (by decide)
  have wNat : (offsetWords input 2).toNat=Guest.GasLimit.le32 input 570 := by simpa [offsetWords] using RawScalar.le32_number input 570
  have bNat : (offsetWords input 3).toNat=Guest.GasLimit.le32 input 590 := by simpa [offsetWords] using RawScalar.le32_number input 590
  have subtraction:=BitVec.toNat_sub_of_le (show offsetWords input 2≤offsetWords input 3 from previous)
  rw [wNat,bNat] at subtraction
  rw [wNat,bNat] at previous
  have upper:=last.2.1
  rw [bNat] at upper
  exact ⟨previous,subtraction,by omega⟩

theorem withdrawal_count_bound (input : Guest.InputBlob) (length : BitVec 64)
    (valid : ∀ position<4,Offsets.ValidAt 540#64 length (offsetWords input) position)
    (inside : 62+length.toNat≤input.length%2^64) :
    withdrawalCount input≤(input.length%2^64)/44 := by
  have facts:=withdrawal_difference input length valid
  unfold withdrawalCount
  omega

theorem withdrawal_count_number (input : Guest.InputBlob) :
    (BitVec.ofNat 64 (withdrawalCount input)).toNat=withdrawalCount input := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  unfold withdrawalCount
  have upper:=RawScalar.le32_lt input 590
  omega

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.withdrawal_difference
#print axioms InitECandidate.Solver.Input.Payload.withdrawal_count_bound

#print axioms InitECandidate.Solver.Input.Payload.withdrawal_count_number
