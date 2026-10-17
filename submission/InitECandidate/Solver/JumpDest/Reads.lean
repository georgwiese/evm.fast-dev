import InitECandidate.Solver.JumpDest.Arithmetic
import InitECandidate.Solver.WitnessRadix.ByteRegion

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

noncomputable def flag (condition : Prop) : BitVec 64 := by
  classical
  exact if condition then 1#64 else 0#64

theorem range_read {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String)
    (word low high : BitVec 64)
    (stored : source.locals.lookup (ofString name) = some (.val (.word word))) :
    eval source (inRange name low high) = some (.val (.word (flag (¬ word < low ∧ ¬ high < word)))) := by
  classical
  by_cases below : word < low <;> by_cases above : high < word <;>
    simp [eval, inRange, truth, localVar, evalHOLExact, evalListHOLExact, toExact, stored,
      flag, valueIsWord, valueWord, wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      below, above]
  all_goals decide

theorem wide_read {F : Type} (source : PanSemStateFiniteExact 64 F) (opcode : BitVec 64)
    (stored : source.locals.lookup (ofString "op") = some (.val (.word opcode))) :
    eval source wideTest = some (.val (.word (flag (opcode = 230#64 ∨ opcode = 231#64)))) := by
  classical
  by_cases first : opcode = 230#64 <;> by_cases second : opcode = 231#64 <;>
    simp [eval, wideTest, truth, localVar, evalHOLExact, evalListHOLExact, toExact, stored,
      flag, valueIsWord, valueWord, wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      first, second]
  all_goals decide

theorem next_test_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index length : BitVec 64)
    (pcLocal : source.locals.lookup (ofString "pc") = some (.val (.word index)))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word length))) :
    eval source hasNext = some (.val (.word (flag (index + 1#64 < length)))) := by
  classical
  simp [eval, hasNext, localVar, evalHOLExact, evalListHOLExact, toExact, pcLocal, nLocal,
    flag, valueIsWord, valueWord, wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

def wordOffset (index : BitVec 64) : BitVec 64 := (index >>> (6 : Nat)) * 8#64

theorem word_offset_number (index : BitVec 64) : (wordOffset index).toNat = index.toNat / 64 * 8 := by
  unfold wordOffset
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (_ / 64 * 8) % 2 ^ 64 = _
  rw [Nat.mod_eq_of_lt (by have bound := index.isLt; omega)]

theorem bitmap_address_read {F : Type} (source : PanSemStateFiniteExact 64 F) (bitmap index : BitVec 64)
    (bitmapLocal : source.locals.lookup (ofString "bm") = some (.val (.word bitmap)))
    (pcLocal : source.locals.lookup (ofString "pc") = some (.val (.word index))) :
    eval source bitmapAddress = some (.val (.word (bitmap + wordOffset index))) := by
  simp [eval, bitmapAddress, wordOffset, localVar, evalHOLExact, evalListHOLExact, toExact,
    bitmapLocal, pcLocal, valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL, panOpHOL]

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.range_read
#print axioms InitECandidate.Solver.JumpDest.wide_read
#print axioms InitECandidate.Solver.JumpDest.next_test_read
#print axioms InitECandidate.Solver.JumpDest.word_offset_number
#print axioms InitECandidate.Solver.JumpDest.bitmap_address_read
