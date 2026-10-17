import InitECandidate.Solver.JumpDest.Program

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def bitmapBytes (length : Nat) : Nat := ((length + 63) / 64) * 8 + 8
def bytesWord (length : BitVec 64) : BitVec 64 := ((length + 63#64) >>> (6 : Nat)) * 8#64 + 8#64

theorem bytes_number (length : BitVec 64) (fits : length.toNat + 63 < 2 ^ 64) :
    (bytesWord length).toNat = bitmapBytes length.toNat := by
  have added : (length + 63#64).toNat = length.toNat + 63 := BitVec.toNat_add_of_lt fits
  have shifted : ((length + 63#64) >>> (6 : Nat)).toNat = (length.toNat + 63) / 64 := by
    rw [BitVec.toNat_ushiftRight, added, Nat.shiftRight_eq_div_pow]
  have multiplied : (((length + 63#64) >>> (6 : Nat)) * 8#64).toNat = (length.toNat + 63) / 64 * 8 := by
    rw [BitVec.toNat_mul, shifted]
    change (_ * 8) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  unfold bytesWord bitmapBytes
  rw [BitVec.toNat_add_of_lt (by rw [multiplied]; change (length.toNat + 63) / 64 * 8 + 8 < 2 ^ 64; omega), multiplied]
  rfl

theorem bytes_read {F : Type} (source : PanSemStateFiniteExact 64 F) (length : BitVec 64)
    (stored : source.locals.lookup (ofString "n") = some (.val (.word length))) :
    eval source bytesExpression = some (.val (.word (bytesWord length))) := by
  simp [eval, bytesExpression, bytesWord, localVar, evalHOLExact, evalListHOLExact, toExact, stored,
    valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL, panOpHOL]

theorem bytes_geometry (length : Nat) :
    bitmapBytes length % 8 = 0 ∧ 8 ≤ bitmapBytes length ∧ bitmapBytes length ≤ length / 8 + 16 := by
  unfold bitmapBytes
  omega

/-- Every bitmap word selected by an in-range byte offset belongs to the
allocated range. The final extra word is included exactly as in the source. -/
theorem selected_word (length index : Nat) (inside : index < length) :
    (index / 64 * 8) + 8 ≤ bitmapBytes length := by
  unfold bitmapBytes
  omega

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.bytes_number
#print axioms InitECandidate.Solver.JumpDest.bytes_read
#print axioms InitECandidate.Solver.JumpDest.bytes_geometry
#print axioms InitECandidate.Solver.JumpDest.selected_word
