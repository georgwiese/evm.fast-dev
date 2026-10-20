import InitECandidate.Solver.Input.PayloadImage

namespace InitECandidate.Solver.Input.Payload
open Flapjack PanSemStateFiniteExact

/-- Validated original payload offsets and extra-data limit, retained for
request hashing's actual variable byte lengths and shared input budgets. -/
structure Layout (input : Guest.InputBlob) (length : BitVec 64) : Prop where
  first : Guest.GasLimit.le32 input 498=540
  extra : Guest.GasLimit.le32 input 566-540≤32
  valid : ∀ position<4,Offsets.ValidAt 540#64 length (offsetWords input) position

theorem Layout.ranges (input : Guest.InputBlob) (length : BitVec 64) (layout : Layout input length) :
    540≤Guest.GasLimit.le32 input 566 ∧ Guest.GasLimit.le32 input 566≤Guest.GasLimit.le32 input 570 ∧
      Guest.GasLimit.le32 input 570≤Guest.GasLimit.le32 input 590 ∧ Guest.GasLimit.le32 input 590≤length.toNat := by
  have first := layout.valid 1 (by decide)
  have second := layout.valid 2 (by decide)
  have last := layout.valid 3 (by decide)
  change 540≤(BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)).toNat ∧ _ at first
  change _ ∧ _ ∧ (0<2→(BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)).toNat≤(BitVec.ofNat 64 (Guest.GasLimit.le32 input 570)).toNat) at second
  change _ ∧ (BitVec.ofNat 64 (Guest.GasLimit.le32 input 590)).toNat≤length.toNat ∧
    (0<3→(BitVec.ofNat 64 (Guest.GasLimit.le32 input 570)).toNat≤(BitVec.ofNat 64 (Guest.GasLimit.le32 input 590)).toNat) at last
  simp only [RawScalar.le32_number] at first second last
  exact ⟨first.1,second.2.2 (by decide),last.2.2 (by decide),last.2.1⟩

theorem Layout.balance_length (input : Guest.InputBlob) (length : BitVec 64) (layout : Layout input length) :
    (length-offsetWords input 3).toNat=length.toNat-Guest.GasLimit.le32 input 590 := by
  have last := (layout.valid 3 (by decide)).2.1
  rw [BitVec.toNat_sub_of_le (show offsetWords input 3≤length from last)]
  have number : (offsetWords input 3).toNat=Guest.GasLimit.le32 input 590 := by simpa [offsetWords] using RawScalar.le32_number input 590
  rw [number]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.Layout.ranges
#print axioms InitECandidate.Solver.Input.Payload.Layout.balance_length
