import InitECandidate.Solver.WitnessRadix.CopyWordByteAway

namespace InitECandidate.Solver.WitnessRadix.CopyByteContent
open Flapjack MutableTable MutableTable.CopyContents

/-- The exact original memcpy reproduces every disjoint source byte and
retains the whole source snapshot, on both the aligned word/byte path and
the fully unaligned byte path. Ordinary extents need not be aligned. -/
theorem full_prefix (memory : WordWrites.Memory) (src dst : BitVec 64) (length : Nat)
    (sourceArena : AllocatedBytes.Arena src length) (destinationArena : AllocatedBytes.Arena dst length)
    (apart : src.toNat+length≤dst.toNat) :
    Prefix memory (CopyGeneral.resultMemory memory false src dst length) src dst length length := by
  have range : Range src dst length:=⟨by have bound:=sourceArena.upper; omega,by have bound:=destinationArena.upper; omega,apart⟩
  by_cases mask : CopyGeneral.aligned src dst
  · rw [CopyGeneral.resultMemory,if_pos mask]
    have parts:=mask
    rw [CopyGeneral.aligned,BitVec.and_or_distrib_right,BitVec.or_eq_zero_iff] at parts
    have sourceAligned : src.toNat%8=0:=by
      have number:=congrArg BitVec.toNat parts.2
      rw [WordBits.mask7] at number
      exact number
    have destinationAligned : dst.toNat%8=0:=by
      have number:=congrArg BitVec.toNat parts.1
      rw [WordBits.mask7] at number
      exact number
    let srcRegion : MemoryRegion.Region:=⟨src.toNat,length⟩
    let dstRegion : MemoryRegion.Region:=⟨dst.toNat,length⟩
    have srcValid : MemoryRegion.Valid srcRegion:=⟨sourceArena.lower,sourceArena.upper,sourceAligned⟩
    have dstValid : MemoryRegion.Valid dstRegion:=⟨destinationArena.lower,destinationArena.upper,destinationAligned⟩
    have srcEq : MemoryRegion.pointer srcRegion=src:=by simp [MemoryRegion.pointer,srcRegion]
    have dstEq : MemoryRegion.pointer dstRegion=dst:=by simp [MemoryRegion.pointer,dstRegion]
    have prefixModel:=aligned_prefix memory srcRegion dstRegion srcValid dstValid (Or.inl apart) length (Nat.le_refl _) (Nat.le_refl _)
    rw [srcEq,dstEq] at prefixModel
    exact prefixModel.suffix memory (CopyGeneral.prefixMemory memory src dst length) src dst length (CopyWords.prefixIndex length) range (CopyWords.prefix_bounds length).1
  · rw [CopyGeneral.resultMemory,if_neg mask]
    exact (prefix_initial memory src dst length).suffix memory memory src dst length 0 range (Nat.zero_le _)

theorem result_byte_at (memory : WordWrites.Memory) (src dst : BitVec 64) (length : Nat)
    (sourceArena : AllocatedBytes.Arena src length) (destinationArena : AllocatedBytes.Arena dst length)
    (apart : src.toNat+length≤dst.toNat) (offset : Nat) (inside : offset<length) :
    byte (CopyGeneral.resultMemory memory false src dst length) (byteAddress dst offset)=byte memory (byteAddress src offset) :=
  (full_prefix memory src dst length sourceArena destinationArena apart).destination offset inside

end InitECandidate.Solver.WitnessRadix.CopyByteContent

#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.full_prefix
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.result_byte_at
