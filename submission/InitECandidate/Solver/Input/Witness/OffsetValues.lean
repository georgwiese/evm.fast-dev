import InitECandidate.Solver.Input.Witness.OffsetProgram
import InitECandidate.Solver.Input.OffsetsAnyLoop
import InitECandidate.Solver.Input.RawScalar

namespace InitECandidate.Solver.Input.Witness
open Flapjack

def offsetNat (input : Guest.InputBlob) (start position : Nat) : Nat:=Guest.GasLimit.le32 input (start+4*position)

theorem offset_number (input : Guest.InputBlob) (start position : Nat) :
    (offsetWord input start position).toNat=offsetNat input start position:=RawScalar.le32_number input _

/-- Mathematical ordered slice extents follow from the actual three-word
validator, including its fixed first offset. No host-size assumption is needed. -/
theorem offset_values (input : Guest.InputBlob) (start : Nat) (total : BitVec 64)
    (first : offsetWord input start 0=12#64)
    (valid : ∀ position<3,Offsets.ValidAt 12#64 total (offsetWord input start) position) :
    offsetNat input start 0=12 ∧ 12≤offsetNat input start 1 ∧
      offsetNat input start 1≤offsetNat input start 2 ∧ offsetNat input start 2≤total.toNat := by
  have firstNumber:=congrArg BitVec.toNat first
  rw [offset_number] at firstNumber
  have middle:=valid 1 (by decide)
  have last:=valid 2 (by decide)
  change 12≤(offsetWord input start 1).toNat ∧ _ at middle
  change _ ∧ (offsetWord input start 2).toNat≤total.toNat ∧
    (0<2 → (offsetWord input start 1).toNat≤(offsetWord input start 2).toNat) at last
  rw [offset_number] at middle
  rw [offset_number,offset_number] at last
  exact ⟨firstNumber,middle.1,last.2.2 (by decide),last.2.1⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.offset_number
#print axioms InitECandidate.Solver.Input.Witness.offset_values
