import InitECandidate.Solver.WitnessRadix.ByteKeys

namespace InitECandidate.Solver.WitnessRadix.WordKeys

/-- The 32 successive little-endian bytes of four 64-bit memory words. -/
def key (words : Fin 4 → BitVec 64) : ByteKeys.Key :=
  fun byte => (words (Fin.ofNat 4 (byte.val / 8)) >>> (8 * (byte.val % 8))).setWidth 8

theorem word_index (byte : Fin 32) :
    (Fin.ofNat 4 (byte.val / 8)).val = byte.val / 8 := by
  change (byte.val / 8) % 4 = byte.val / 8
  apply Nat.mod_eq_of_lt
  have := byte.isLt
  omega

/-- Equality of the actual four loaded words is equivalent to equality of
all 32 model key bytes. Neither direction assumes aligned query addresses;
the caller establishes which words constitute its key. -/
theorem injective (left right : Fin 4 → BitVec 64) (same : key left = key right) : left = right := by
  funext word
  apply BitVec.eq_of_getLsbD_eq
  intro digit digitInside
  let byte : Fin 32 := ⟨8 * word.val + digit / 8, by have := word.isLt; omega⟩
  have div : byte.val / 8 = word.val := by dsimp [byte]; omega
  have rem : byte.val % 8 = digit / 8 := by dsimp [byte]; omega
  have index : Fin.ofNat 4 (byte.val / 8) = word := by
    apply Fin.ext
    rw [word_index byte, div]
  have byteEq := congrFun same byte
  have bitEq := congrArg (fun value : BitVec 8 => value.getLsbD (digit % 8)) byteEq
  simp only [key, index, rem, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at bitEq
  have small : digit % 8 < 8 := by omega
  have decompose : 8 * (digit / 8) + digit % 8 = digit := by omega
  simpa only [small, decide_true, Bool.true_and, decompose] using bitEq

theorem equal_iff (left right : Fin 4 → BitVec 64) : key left = key right ↔ left = right :=
  ⟨injective left right, congrArg key⟩

end InitECandidate.Solver.WitnessRadix.WordKeys

#print axioms InitECandidate.Solver.WitnessRadix.WordKeys.injective
#print axioms InitECandidate.Solver.WitnessRadix.WordKeys.equal_iff
