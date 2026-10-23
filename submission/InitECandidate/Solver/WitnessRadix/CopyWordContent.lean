import InitECandidate.Solver.WitnessRadix.CopyBytePrefix
import InitECandidate.Solver.MutableTable.CopyUsedContents

namespace InitECandidate.Solver.WitnessRadix.CopyByteContent
open Flapjack MutableTable.CopyContents
open MutableTable

/-- Discarding the partial last word leaves the exact original memcpy
word-prefix loops and stores unchanged. -/
theorem prefix_memory_truncate (memory : WordWrites.Memory) (src dst : BitVec 64) (length : Nat) :
    CopyGeneral.prefixMemory memory src dst length=CopyGeneral.prefixMemory memory src dst (CopyWords.prefixIndex length) := by
  have first : CopyWords.prefixIndex length/32=length/32:=by unfold CopyWords.prefixIndex; omega
  have second : (CopyWords.prefixIndex length%32)/8=(length%32)/8:=by unfold CopyWords.prefixIndex; omega
  simp only [CopyGeneral.prefixMemory,first,second]

theorem prefix_words_away (memory : WordWrites.Memory) (src dst query : BitVec 64) (length : Nat)
    (away : ∀ offset<length,query≠byteAddress dst offset) :
    CopyGeneral.prefixMemory memory src dst length query=memory query := by
  have before:=(CopyWords.prefix_bounds length).1
  unfold CopyWords.prefixIndex at before
  unfold CopyGeneral.prefixMemory
  rw [CopyWords.memoryWalk_away _ _ _ _ _ _ _ _ (by intro offset member; simp at member; subst offset; decide)
    (by intro offset low high; exact away offset (by omega))]
  apply CopyWords.memoryWalk_away
  · intro offset member
    simp [CopyWords.wordOffsets] at member
    omega
  · intro offset low high
    exact away offset (by omega)

/-- The exact aligned prefix reproduces every full-word byte, while
preserving all bytes in its disjoint source interval. Partial tails are
handled by the separate original byte loops. -/
theorem aligned_prefix (memory : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start+src.length≤dst.start ∨ dst.start+dst.length≤src.start)
    (length : Nat) (srcRoom : length≤src.length) (dstRoom : length≤dst.length) :
    Prefix memory (CopyGeneral.prefixMemory memory (MemoryRegion.pointer src) (MemoryRegion.pointer dst) length)
      (MemoryRegion.pointer src) (MemoryRegion.pointer dst) length (CopyWords.prefixIndex length) := by
  have before:=(CopyWords.prefix_bounds length).1
  have multiple : CopyWords.prefixIndex length%8=0:=by unfold CopyWords.prefixIndex; omega
  constructor
  · intro query inside
    unfold byte
    rw [backing_address src srcValid query (by omega)]
    rw [prefix_words_away _ _ _ _ _ (by
      intro offset inCopy
      exact MemoryRegion.separate src dst srcValid dstValid apart (8*(query/8)) offset (by omega) (by omega))]
  · intro query inside
    unfold byte
    rw [backing_address dst dstValid query (by omega),prefix_memory_truncate]
    rw [prefix_at memory src dst srcValid dstValid apart (CopyWords.prefixIndex length) (by omega) (by omega) multiple (8*(query/8)) (by omega) (by omega)]
    rw [same_lane src dst srcValid dstValid query (by omega) (by omega),backing_address src srcValid query (by omega)]

end InitECandidate.Solver.WitnessRadix.CopyByteContent

#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.prefix_memory_truncate
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.prefix_words_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.aligned_prefix
