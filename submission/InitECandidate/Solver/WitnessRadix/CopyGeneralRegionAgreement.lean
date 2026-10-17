import InitECandidate.Solver.WitnessRadix.CopyRegionAgreement

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack MemoryRegion

theorem prefixMemory_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (src dst : BitVec 64) (length : Nat)
    (reads : ∀ offset < length, offset % 8 = 0 → region (byteAddress src offset)) :
    Agree region (prefixMemory left src dst length) (prefixMemory right src dst length) := by
  have bounds := (CopyWords.prefix_bounds length).1
  have first := CopyWords.memoryWalk_agrees region left right same src dst 0 32 CopyWords.wordOffsets (length / 32)
    (by intro offset member; simp [CopyWords.wordOffsets] at member; omega) (by decide) (by decide)
    (by intro offset member; simp [CopyWords.wordOffsets] at member; rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro offset low high aligned; exact reads offset (by unfold CopyWords.prefixIndex at bounds; omega) aligned)
  apply CopyWords.memoryWalk_agrees region _ _ first src dst (32 * (length / 32)) 8 [0] ((length % 32) / 8)
  · intro offset member; simp at member; omega
  · omega
  · decide
  · intro offset member; simp at member; subst offset; decide
  · intro offset low high aligned
    exact reads offset (by unfold CopyWords.prefixIndex at bounds; omega) aligned

theorem suffixMemory_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (endian : Bool) (src dst : BitVec 64) (index length : Nat)
    (ordered : index ≤ length)
    (reads : ∀ offset < length,
      region (panByteAlignHOL (width := 64) (byteAddress src offset))) :
    Agree region (suffixMemory left endian src dst index length) (suffixMemory right endian src dst index length) := by
  have div := Nat.mod_add_div (length - index) 8
  have first := CopyBytes.memoryWalk_agrees region left right same endian src dst index 8 CopyBytes.byteOffsets ((length - index) / 8)
    (by intro offset member; simp [CopyBytes.byteOffsets] at member; omega)
    (by intro offset low high; exact reads offset (by omega))
  apply CopyBytes.memoryWalk_agrees region _ _ first endian src dst
    (index + 8 * ((length - index) / 8)) 1 [0] ((length - index) % 8)
  · intro offset member; simp at member; omega
  · intro offset low high
    exact reads offset (by omega)

/-- Exact memcpy memory, including aligned word prefixes and byte tails,
respects agreement on a region containing its input read cells. -/
theorem resultMemory_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (endian : Bool) (src dst : BitVec 64) (length : Nat)
    (wordReads : aligned src dst → ∀ offset < length, offset % 8 = 0 →
      region (byteAddress src offset))
    (byteReads : ∀ offset < length,
      region (panByteAlignHOL (width := 64) (byteAddress src offset))) :
    Agree region (resultMemory left endian src dst length) (resultMemory right endian src dst length) := by
  unfold resultMemory
  split
  · rename_i mask
    exact suffixMemory_agrees region _ _ (prefixMemory_agrees region left right same src dst length (wordReads mask))
      endian src dst (CopyWords.prefixIndex length) length (CopyWords.prefix_bounds length).1 byteReads
  · exact suffixMemory_agrees region left right same endian src dst 0 length (Nat.zero_le _) byteReads

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.prefixMemory_agrees
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.suffixMemory_agrees
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.resultMemory_agrees
