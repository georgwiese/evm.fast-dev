import InitECandidate.Solver.Input.CurrentTable.FirstDiff.Program
import InitECandidate.Solver.Input.CurrentTable.KeyBits

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm

theorem bit_test_shape : bitTest = .cmp .notEqual
    (.op .and [.shift .lsr (localVar "x") (.op .sub [.const 7#64,localVar "j"]),.const 1#64])
    (.const 0#64) := by
  simp only [bitTest,bitGuard,bitStep,bitLoop,different,choice,afterX,step,loop,afterI,body,
    Guest.Software.guestFn_htab_first_diff,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

/-- The actual shifted low-bit mask observes the selected source word bit. -/
theorem masked_bit (word : BitVec 64) (position : Nat) :
    ((word >>> position) &&& 1#64) = (if word.getLsbD position then 1#64 else 0#64) := by
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  simp only [BitVec.getLsbD_ushiftRight,Nat.zero_add]
  cases word.getLsbD position <;> rfl

/-- Actual source bit test, in its nonnegative signed j-counter range. -/
theorem bit_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (word : BitVec 64) (position : Nat) (inside : position < 8)
    (wordCell : source.locals.lookup (ofString "x") = some (.val (.word word)))
    (counterCell : source.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 position)))) :
    eval source bitTest = some (.val (.word (if word.getLsbD (7-position) then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 position).toNat = position := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have difference : (7#64-BitVec.ofNat 64 position).toNat = 7-position := by
    rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 position).toNat ≤ 7; rw [number]; omega),number]
    rfl
  rw [bit_test_shape]
  have oneMask : AndOp.and (1#64 : BitVec 64) 18446744073709551615#64 = 1#64 := by decide
  have observedMask : AndOp.and (word >>> (7-position)) 1#64 =
      (if word.getLsbD (7-position) then 1#64 else 0#64) := masked_bit word (7-position)
  simp [eval,evalHOLExact,evalListHOLExact,localVar,wordCell,counterCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL,difference,
    show ¬(7-position ≠ 0 ∧ 64 ≤ 7-position) from by omega,oneMask,observedMask,wordCmpHOL]

/-- Widening byte xor retains the current most-significant-first digit. -/
theorem xor_digit (left right : BitVec 8) (position : Nat) (inside : position < 8) :
    ((left.setWidth 64) ^^^ (right.setWidth 64)).getLsbD (7-position) =
      Bool.xor (left.getLsbD (7-position)) (right.getLsbD (7-position)) := by
  simp [BitVec.getLsbD_xor,BitVec.getLsbD_setWidth,show 7-position < 64 from by omega]

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.masked_bit
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.bit_test_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.xor_digit
