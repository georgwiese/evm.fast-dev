import InitECandidate.Solver.MutableTable.CopyByteContents

namespace InitECandidate.Solver.MutableTable.CopyContents
open Flapjack WitnessRadix

theorem backing_address (region : MemoryRegion.Region) (valid : MemoryRegion.Valid region)
    (query : Nat) (inside : query < region.length) :
    panByteAlignHOL (width := 64) (byteAddress (MemoryRegion.pointer region) query) =
      byteAddress (MemoryRegion.pointer region) (8 * (query / 8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [MemoryRegion.aligned_number region valid query inside, MemoryRegion.byte_address,
    MemoryRegion.address_number region valid (8 * (query / 8)) (by omega)]

theorem same_lane (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (query : Nat) (srcInside : query < src.length) (dstInside : query < dst.length) (word : BitVec 64) :
    panGetByteHOL (byteAddress (MemoryRegion.pointer dst) query) word false =
      panGetByteHOL (byteAddress (MemoryRegion.pointer src) query) word false := by
  have lanes : (byteAddress (MemoryRegion.pointer dst) query).toNat % 8 = (byteAddress (MemoryRegion.pointer src) query).toNat % 8 := by
    rw [MemoryRegion.byte_address, MemoryRegion.address_number dst dstValid query (by omega),
      MemoryRegion.byte_address, MemoryRegion.address_number src srcValid query (by omega)]
    simp only [Nat.add_mod, dstValid.aligned, srcValid.aligned, Nat.zero_add]
  simp only [panGetByteHOL, Bool.false_eq_true, if_false, lanes]

theorem aligned_bytes_at (input : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (length : Nat) (srcRoom : length ≤ src.length) (dstRoom : length ≤ dst.length)
    (multiple : length % 8 = 0) (query : Nat) (inside : query < length) :
    byte (CopyGeneral.resultMemory input false (MemoryRegion.pointer src) (MemoryRegion.pointer dst) length)
      (byteAddress (MemoryRegion.pointer dst) query) = byte input (byteAddress (MemoryRegion.pointer src) query) := by
  unfold byte
  rw [backing_address dst dstValid query (by omega),
    word_at input false src dst srcValid dstValid apart length srcRoom dstRoom multiple (8 * (query / 8)) (by omega) (by omega),
    same_lane src dst srcValid dstValid query (by omega) (by omega), backing_address src srcValid query (by omega)]

/-- Used-array copies at both supported capacity shapes preserve every
logical flag, without requiring the unused padding bytes to be copied. -/
theorem used_bytes_at (input : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (length : Nat) (srcRoom : length ≤ src.length) (dstRoom : length ≤ dst.length)
    (shape : length = 4 ∨ length % 8 = 0) (query : Nat) (inside : query < length) :
    byte (CopyGeneral.resultMemory input false (MemoryRegion.pointer src) (MemoryRegion.pointer dst) length)
      (byteAddress (MemoryRegion.pointer dst) query) = byte input (byteAddress (MemoryRegion.pointer src) query) := by
  rcases shape with rfl | multiple
  · exact four_bytes_at input src dst srcValid dstValid apart srcRoom dstRoom query inside
  · exact aligned_bytes_at input src dst srcValid dstValid apart length srcRoom dstRoom multiple query inside

end InitECandidate.Solver.MutableTable.CopyContents

#print axioms InitECandidate.Solver.MutableTable.CopyContents.backing_address
#print axioms InitECandidate.Solver.MutableTable.CopyContents.same_lane
#print axioms InitECandidate.Solver.MutableTable.CopyContents.aligned_bytes_at
#print axioms InitECandidate.Solver.MutableTable.CopyContents.used_bytes_at
