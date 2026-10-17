import InitECandidate.Solver.WitnessRadix.MemeqByteTail

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack

theorem byteChecks_agree_iff (left right : Fin 8 → BitVec 64) :
    CompareChain.agrees (byteChecks left right) = true ↔ left = right := by
  simp [CompareChain.agrees, byteChecks, funext_iff, Fin.forall_fin_succ]

theorem allBlocks_agree_iff (left right : Fin 4 → Fin 8 → BitVec 64) :
    allBlocks left right 0 4 = true ↔ left = right := by
  simp [allBlocks, byteChecks_agree_iff, funext_iff, Fin.forall_fin_succ]

def chunks (key : ByteKeys.Key) : Fin 4 → Fin 8 → BitVec 64 :=
  fun block offset => (key ⟨8 * block.val + offset.val, by have := block.isLt; have := offset.isLt; omega⟩).setWidth 64

theorem chunks_injective (left right : ByteKeys.Key) (same : chunks left = chunks right) : left = right := by
  funext byte
  let block : Fin 4 := ⟨byte.val / 8, by have := byte.isLt; omega⟩
  let offset : Fin 8 := ⟨byte.val % 8, by omega⟩
  have index : (⟨8 * block.val + offset.val, by have := block.isLt; have := offset.isLt; omega⟩ : Fin 32) = byte := by
    apply Fin.ext
    dsimp [block, offset]
    omega
  have word := congrFun (congrFun same block) offset
  have narrowed := congrArg (BitVec.setWidth 8) word
  simpa [chunks, index] using narrowed

theorem chunks_equal_iff (left right : ByteKeys.Key) : chunks left = chunks right ↔ left = right :=
  ⟨chunks_injective left right, congrArg chunks⟩

theorem allBytes_agree_iff (left right : ByteKeys.Key) :
    allBlocks (chunks left) (chunks right) 0 4 = true ↔ left = right := by
  rw [allBlocks_agree_iff, chunks_equal_iff]

def toUInt8 (byte : BitVec 8) : UInt8 := UInt8.ofNat byte.toNat

theorem widened_byte (byte : BitVec 8) :
    BitVec.ofNat 64 (toUInt8 byte).toNat = byte.setWidth 64 := by
  have small := byte.isLt
  have natural : (toUInt8 byte).toNat = byte.toNat := by
    simp [toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt small]
  rw [natural]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth_of_le (by decide), Nat.mod_eq_of_lt (by omega)]

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.byteChecks_agree_iff
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.allBytes_agree_iff
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.widened_byte
