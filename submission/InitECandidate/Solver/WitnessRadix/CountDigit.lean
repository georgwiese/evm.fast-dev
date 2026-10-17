import InitECandidate.Solver.WitnessRadix.CountProgram
import InitECandidate.Solver.WitnessRadix.QueryMemory

namespace InitECandidate.Solver.WitnessRadix.CountProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

private theorem andOnes (word : BitVec 64) :
    AndOp.and word (18446744073709551615#64) = word := by
  change word &&& BitVec.allOnes 64 = word
  exact BitVec.and_allOnes

private theorem opAnd (left right : BitVec 64) :
    wordOpHOL .and [left, right] = some (left &&& right) := by
  change some (AndOp.and left (AndOp.and right (18446744073709551615#64))) = _
  rw [andOnes]
  rfl

private theorem opAdd3 (a b c : BitVec 64) :
    wordOpHOL .add [a,b,c] = some (a + (b + c)) := by
  simp [wordOpHOL, wordOp]

theorem digit_read {F : Type} (source : PanSemStateFiniteExact 64 F)
    (keys ordinal position : BitVec 64) (byte : UInt8)
    (keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word position)))
    (loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      ((keys + ordinal * 32#64) + (position >>> (3 : Nat))) = some byte) :
    eval source digitExpression =
      some (.val (.word (WordBits.digit (BitVec.ofNat 8 byte.toNat) position))) := by
  classical
  have shiftSmall : ¬ ((position &&& 7#64).toNat ≠ 0 ∧ 64 ≤ (position &&& 7#64).toNat) := by
    rw [WordBits.mask7]
    omega
  have widened : BitVec.ofNat 64 byte.toNat = (BitVec.ofNat 8 byte.toNat).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    have small : byte.toNat < 256 := byte.toNat_lt_size
    simp [Nat.mod_eq_of_lt (show byte.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt small]
  have threeNat : (3#64).toNat = 3 := rfl
  have threeFits : ¬ (3 ≠ 0 ∧ 64 ≤ (3 : Nat)) := by decide
  simp only [eval, digitExpression, localVar, evalHOLExact, evalListHOLExact, toExact,
    keysLocal, ordinalLocal, bitLocal, valueIsWord, valueWord, List.all_cons, List.all_nil,
    Bool.and_self, Bool.and_true, List.map_cons, List.map_nil, opAnd, opAdd3, panOpHOL,
    Option.map_some, ↓reduceIte, wordShiftHOL, threeNat, threeFits, shiftSmall]
  rw [← BitVec.add_assoc, loaded]
  simp only [Option.map_some, shiftSmall, ↓reduceIte, List.all_cons, List.all_nil,
    valueIsWord, Bool.and_self, List.map_cons, List.map_nil, valueWord, opAnd]
  rw [widened]
  rfl

end InitECandidate.Solver.WitnessRadix.CountProgram

#print axioms InitECandidate.Solver.WitnessRadix.CountProgram.digit_read
