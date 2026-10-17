import InitECandidate.Solver.MutableTable.HashCall32
import InitECandidate.Solver.Input.Scalar64

namespace InitECandidate.Solver.MutableTable.Hash
open Flapjack

def extractedByte (word : BitVec 64) (index : Nat) : BitVec 64:=((word >>> (8*index)).setWidth 8).setWidth 64

set_option maxHeartbeats 1000000 in
/-- Rebuilding a word from the eight byte extractions used by the unaligned
hash path gives exactly the aligned word, without an endian assumption here. -/
theorem rebuild_word (word : BitVec 64) :
    Input.WordCodec.word8 (extractedByte word 0) (extractedByte word 1) (extractedByte word 2) (extractedByte word 3)
      (extractedByte word 4) (extractedByte word 5) (extractedByte word 6) (extractedByte word 7)=word := by
  let byte : Nat→BitVec 8:=fun i=>(word >>> (8*i)).setWidth 8
  have assembled:=Input.WordCodec.word8_eq (byte 0).toNat (byte 1).toNat (byte 2).toNat (byte 3).toNat
    (byte 4).toNat (byte 5).toNat (byte 6).toNat (byte 7).toNat
    (byte 0).isLt (byte 1).isLt (byte 2).isLt (byte 3).isLt (byte 4).isLt (byte 5).isLt (byte 6).isLt (byte 7).isLt
  have widened : ∀ i,extractedByte word i=BitVec.ofNat 64 (byte i).toNat := by
    intro i
    apply BitVec.eq_of_toNat_eq
    simp [extractedByte,byte,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  simp only [widened]
  rw [assembled]
  apply BitVec.eq_of_toNat_eq
  have bounded:=word.isLt
  simp only [byte,BitVec.toNat_ofNat,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  omega

end InitECandidate.Solver.MutableTable.Hash

#print axioms InitECandidate.Solver.MutableTable.Hash.rebuild_word
