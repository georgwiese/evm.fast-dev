import InitECandidate.Solver.Input.CurrentTable.FirstDiff.BitLoopReturned

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

private theorem xor_clear {a b : Bool} (zero : Bool.xor a b = false) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem xor_set {a b : Bool} (one : Bool.xor a b = true) : a ≠ b := by
  cases a <;> cases b <;> simp_all

/-- Combine the real byte scan's least digit with agreement of all earlier
bytes, in the current most-significant-first Patricia bit order. -/
theorem byte_answer (left right : KeyBits.Key) (index : Fin 32)
    (earlier : ∀ prior : Fin 32,prior.val < index.val → left prior = right prior)
    (value : ValueHOL 64) (answer : BitAnswer (left index ^^^ right index) (BitVec.ofNat 64 index.val) value) :
    ∃ position : Nat,position < 256 ∧ value = .val (.word (BitVec.ofNat 64 position)) ∧ KeyBits.First left right position := by
  obtain ⟨digit,inside,valueEq,different,before⟩ := answer
  let position := 8*index.val+digit
  have bounded : position < 256 := by dsimp [position]; have := index.isLt; omega
  have quotient : position/8 = index.val := by dsimp [position]; omega
  have remainder : position%8 = digit := by dsimp [position]; omega
  have selected : Fin.ofNat 32 (position/8) = index := by
    apply Fin.ext
    rw [KeyBits.byte_index position bounded,quotient]
  refine ⟨position,bounded,?_,⟨by omega,?_,?_⟩⟩
  · rw [valueEq]
    congr 3
    dsimp [position]
    rw [BitVec.ofNat_add,BitVec.ofNat_mul]
    simp only [Nat.mul_comm,BitVec.mul_comm]
  · intro prior smaller
    have priorInside : prior < 256 := by omega
    have leByte : prior/8 ≤ index.val := by dsimp [position] at smaller; omega
    by_cases previous : prior/8 < index.val
    · have equal := earlier (Fin.ofNat 32 (prior/8)) (by rw [KeyBits.byte_index prior priorInside]; exact previous)
      simp only [KeyBits.bit,equal]
    · have sameByte : prior/8 = index.val := by omega
      have sameIndex : Fin.ofNat 32 (prior/8) = index := by
        apply Fin.ext
        rw [KeyBits.byte_index prior priorInside,sameByte]
      have smallerDigit : prior%8 < digit := by dsimp [position] at smaller; omega
      have clear := before (prior%8) smallerDigit
      simp only [BitVec.getLsbD_xor] at clear
      simpa only [KeyBits.bit,sameIndex] using xor_clear clear
  · intro inRange
    simp only [BitVec.getLsbD_xor] at different
    simpa only [KeyBits.bit,selected,remainder] using xor_set different

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.byte_answer
