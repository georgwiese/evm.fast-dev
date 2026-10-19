import InitECandidate.Solver.Mpt.KeyToNibblesProgram
import InitECandidate.Solver.WitnessRadix.ByteStoreRead

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def high (byte : BitVec 8) : BitVec 8 := byte >>> (4 : Nat)
def low (byte : BitVec 8) : BitVec 8 := byte &&& 15#8

theorem high_small (byte : BitVec 8) : (high byte).toNat < 16 := by
  have small := byte.isLt
  simp only [high, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega
theorem low_small (byte : BitVec 8) : (low byte).toNat < 16 := by
  have bounded : byte.toNat &&& 15 ≤ 15 := Nat.and_le_right
  simp only [low, BitVec.toNat_and]
  change byte.toNat &&& 15 < 16
  omega

theorem high_wide (byte : BitVec 8) :
    (BitVec.ofNat 64 byte.toNat >>> (4 : Nat)) = BitVec.ofNat 64 (high byte).toNat := by
  apply BitVec.eq_of_toNat_eq
  have byteWide : byte.toNat < 2^64 := by have small := byte.isLt; omega
  have highWide : (high byte).toNat < 2^64 := by have small := high_small byte; omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt byteWide,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt highWide]
  exact (BitVec.toNat_ushiftRight byte 4).symm

theorem low_wide (byte : BitVec 8) :
    (BitVec.ofNat 64 byte.toNat &&& 15#64) = BitVec.ofNat 64 (low byte).toNat := by
  apply BitVec.eq_of_toNat_eq
  have byteWide : byte.toNat < 2^64 := by have small := byte.isLt; omega
  have lowWide : (low byte).toNat < 2^64 := by have small := low_small byte; omega
  have bound : byte.toNat &&& 15 < 2^64 := by
    have small : byte.toNat &&& 15 ≤ 15 := Nat.and_le_right
    omega
  simp [low, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt byteWide, Nat.mod_eq_of_lt bound]

theorem output_read {F : Type} (source : PanSemStateFiniteExact 64 F) (out index : BitVec 64) (offset : Nat)
    (outCell : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexCell : source.locals.lookup (ofString "i") = some (.val (.word index))) :
    eval source (outputAddress offset) = some (.val (.word (out + 2#64 * index + BitVec.ofNat 64 offset))) := by
  by_cases zero : offset = 0
  · subst offset
    simp [outputAddress, eval, evalHOLExact, evalListHOLExact, localVar, toExact, outCell, indexCell,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
  · simp [outputAddress, zero, eval, evalHOLExact, evalListHOLExact, localVar, toExact, outCell, indexCell,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_assoc]

theorem high_read {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (byte : BitVec 8)
    (cell : source.locals.lookup (ofString name) = some (.val (.word (BitVec.ofNat 64 byte.toNat)))) :
    eval source (.shift .lsr (localVar name) (.const 4#64)) = some (.val (.word (BitVec.ofNat 64 (high byte).toNat))) := by
  simp [eval, evalHOLExact, localVar, toExact, cell, wordShiftHOL]
  simpa only [BitVec.ofNat_toNat] using high_wide byte

theorem low_read {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (byte : BitVec 8)
    (cell : source.locals.lookup (ofString name) = some (.val (.word (BitVec.ofNat 64 byte.toNat)))) :
    eval source (.op .and [localVar name, .const 15#64]) = some (.val (.word (BitVec.ofNat 64 (low byte).toNat))) := by
  simp [eval, evalHOLExact, evalListHOLExact, localVar, toExact, cell,
    valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and]
  simpa only [BitVec.ofNat_toNat] using low_wide byte

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.high_small
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.low_small
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.high_wide
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.low_wide
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.output_read
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.high_read
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.low_read
