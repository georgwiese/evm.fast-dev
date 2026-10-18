import InitECandidate.Solver.MutableTable.CopyAlignedContents
import InitECandidate.Solver.MutableTable.ByteStore

namespace InitECandidate.Solver.MutableTable.CopyContents
open Flapjack WitnessRadix

def byte (memory : WordWrites.Memory) (address : BitVec 64) : UInt8 :=
  panGetByteHOL address (MemoryBytes.wordBits (memory (panByteAlignHOL (width := 64) address))) false

/-- Projection of the actual byte copy, including other lanes in the same
destination word. -/
theorem byte_copy_projection (input : WordWrites.Memory) (src dst index query : BitVec 64) (offset : Nat) :
    byte (CopyBytes.copyMemory input false src dst index offset) query =
      if query = dst + index + BitVec.ofNat 64 offset then byte input (src + index + BitVec.ofNat 64 offset) else byte input query := by
  have bridge : CopyBytes.copyMemory input false src dst index offset =
      ByteStore.write input (dst + index + BitVec.ofNat 64 offset) (byte input (src + index + BitVec.ofNat 64 offset)) := by
    unfold CopyBytes.copyMemory WitnessRadix.ByteStore.put ByteStore.write byte
    rw [panGetByteHOL_toNat_eq_word8]
  rw [bridge]
  exact ByteStore.projection input _ query _

theorem byte_tail_away (input : WordWrites.Memory) (src dst query : BitVec 64) (index rounds : Nat)
    (away : ∀ offset, index ≤ offset → offset < index + rounds → query ≠ byteAddress dst offset) :
    byte (CopyBytes.memoryWalk input false src dst index 1 [0] rounds) query = byte input query := by
  induction rounds generalizing input index with
  | zero => rfl
  | succ rounds ih =>
    rw [CopyBytes.memoryWalk, ih _ (index + 1) (by intro offset low high; exact away offset (by omega) (by omega))]
    simp only [CopyBytes.memoryMany, byte_copy_projection, indexed_byte]
    rw [if_neg (by simpa only [Nat.add_zero] using away index (by omega) (by omega))]

theorem byte_tail_at (input snapshot : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (index rounds : Nat) (srcRoom : index + rounds ≤ src.length) (dstRoom : index + rounds ≤ dst.length)
    (sourceKept : ∀ offset < src.length, byte input (byteAddress (MemoryRegion.pointer src) offset) = byte snapshot (byteAddress (MemoryRegion.pointer src) offset))
    (query : Nat) (inside : query < rounds) :
    byte (CopyBytes.memoryWalk input false (MemoryRegion.pointer src) (MemoryRegion.pointer dst) index 1 [0] rounds)
      (byteAddress (MemoryRegion.pointer dst) (index + query)) = byte snapshot (byteAddress (MemoryRegion.pointer src) (index + query)) := by
  induction rounds generalizing input index query with
  | zero => omega
  | succ rounds ih =>
    let first := CopyBytes.copyMemory input false (MemoryRegion.pointer src) (MemoryRegion.pointer dst) (BitVec.ofNat 64 index) 0
    have retained : ∀ offset < src.length, byte first (byteAddress (MemoryRegion.pointer src) offset) = byte snapshot (byteAddress (MemoryRegion.pointer src) offset) := by
      intro offset offsetInside
      dsimp only [first]
      rw [byte_copy_projection, indexed_byte, Nat.add_zero, if_neg (MemoryRegion.separate src dst srcValid dstValid apart offset index offsetInside (by omega))]
      exact sourceKept offset offsetInside
    cases query with
    | zero =>
      simp only [Nat.add_zero]
      rw [CopyBytes.memoryWalk]
      change byte (CopyBytes.memoryWalk first false (MemoryRegion.pointer src) (MemoryRegion.pointer dst) (index + 1) 1 [0] rounds) _ = _
      rw [byte_tail_away first _ _ _ (index + 1) rounds (by
        intro offset lower upper same
        have equal := MemoryRegion.byte_address_injective dst dstValid index offset (by omega) (by omega) same
        omega)]
      dsimp only [first]
      rw [byte_copy_projection, indexed_byte, Nat.add_zero, if_pos rfl, indexed_byte, Nat.add_zero]
      exact sourceKept index (by omega)
    | succ query =>
      have tail := ih first (index + 1) (by omega) (by omega) retained query (by omega)
      have selected : index + 1 + query = index + (query + 1) := by omega
      rw [selected] at tail
      exact tail

/-- The original aligned four-byte used-array copy reproduces each flag. -/
theorem four_bytes_at (input : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (srcRoom : 4 ≤ src.length) (dstRoom : 4 ≤ dst.length) (query : Nat) (inside : query < 4) :
    byte (CopyGeneral.resultMemory input false (MemoryRegion.pointer src) (MemoryRegion.pointer dst) 4)
      (byteAddress (MemoryRegion.pointer dst) query) = byte input (byteAddress (MemoryRegion.pointer src) query) := by
  rw [CopyGeneral.resultMemory, if_pos (regions_aligned src dst srcValid dstValid)]
  simp only [CopyGeneral.prefixMemory, CopyWords.prefixIndex, CopyWords.memoryWalk,
    CopyGeneral.suffixMemory, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, CopyBytes.memoryWalk]
  simpa only [CopyBytes.memoryWalk, Nat.zero_add, Nat.reduceAdd] using
    byte_tail_at input input src dst srcValid dstValid apart 0 4 (by omega) (by omega) (by intro offset h; rfl) query inside

end InitECandidate.Solver.MutableTable.CopyContents

#print axioms InitECandidate.Solver.MutableTable.CopyContents.byte_copy_projection
#print axioms InitECandidate.Solver.MutableTable.CopyContents.byte_tail_away
#print axioms InitECandidate.Solver.MutableTable.CopyContents.byte_tail_at
#print axioms InitECandidate.Solver.MutableTable.CopyContents.four_bytes_at
