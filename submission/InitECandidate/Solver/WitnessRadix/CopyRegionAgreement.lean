import InitECandidate.Solver.WitnessRadix.MemoryRegionAgreement
import InitECandidate.Solver.WitnessRadix.CopyGeneralMemoryResult

namespace InitECandidate.Solver.WitnessRadix.CopyBytes
open Flapjack MemoryRegion

theorem memoryMany_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (endian : Bool) (src dst index : BitVec 64) (offsets : List Nat)
    (reads : ∀ offset ∈ offsets,
      region (panByteAlignHOL (width := 64) (src + index + BitVec.ofNat 64 offset))) :
    Agree region (memoryMany left endian src dst index offsets) (memoryMany right endian src dst index offsets) := by
  induction offsets generalizing left right with
  | nil => exact same
  | cons offset rest ih =>
    have readEq := same _ (reads offset (by simp))
    have next := MemoryRegion.byte_put region left right same endian
      (dst + index + BitVec.ofNat 64 offset)
      (panGetByteWord8HOL (src + index + BitVec.ofNat 64 offset)
        (MemoryBytes.wordBits (right (panByteAlignHOL (width := 64) (src + index + BitVec.ofNat 64 offset)))) endian)
    have nextSame : Agree region (copyMemory left endian src dst index offset)
        (copyMemory right endian src dst index offset) := by
      simpa only [copyMemory, readEq] using next
    exact ih _ _ nextSame (by intro offset member; exact reads offset (List.mem_cons_of_mem _ member))

theorem memoryWalk_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (endian : Bool) (src dst : BitVec 64)
    (index step : Nat) (offsets : List Nat) (rounds : Nat)
    (bounded : ∀ offset ∈ offsets, offset < step)
    (reads : ∀ offset, index ≤ offset → offset < index + step * rounds →
      region (panByteAlignHOL (width := 64) (byteAddress src offset))) :
    Agree region (memoryWalk left endian src dst index step offsets rounds)
      (memoryWalk right endian src dst index step offsets rounds) := by
  induction rounds generalizing left right index with
  | zero => exact same
  | succ rounds ih =>
    have next := memoryMany_agrees region left right same endian src dst (BitVec.ofNat 64 index) offsets (by
      intro offset member
      have cell := reads (index + offset) (by omega) (by
        have := bounded offset member
        simp only [Nat.mul_succ]
        omega)
      simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using cell)
    exact ih _ _ next (index + step) (by
      intro offset low high
      apply reads offset (by omega)
      simp only [Nat.mul_succ]
      omega)

end InitECandidate.Solver.WitnessRadix.CopyBytes

namespace InitECandidate.Solver.WitnessRadix.CopyWords
open Flapjack MemoryRegion

theorem memoryMany_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (src dst index : BitVec 64) (offsets : List Nat)
    (reads : ∀ offset ∈ offsets, region (src + index + BitVec.ofNat 64 offset)) :
    Agree region (memoryMany left src dst index offsets) (memoryMany right src dst index offsets) := by
  induction offsets generalizing left right with
  | nil => exact same
  | cons offset rest ih =>
    have readEq := same _ (reads offset (by simp))
    have next := MemoryRegion.word_put region left right same (dst + index + BitVec.ofNat 64 offset)
      (MemoryBytes.wordBits (right (src + index + BitVec.ofNat 64 offset)))
    have nextSame : Agree region (copyMemory left src dst index offset)
        (copyMemory right src dst index offset) := by
      simpa only [copyMemory, readEq] using next
    exact ih _ _ nextSame (by intro offset member; exact reads offset (List.mem_cons_of_mem _ member))

theorem memoryWalk_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (src dst : BitVec 64)
    (index step : Nat) (offsets : List Nat) (rounds : Nat)
    (bounded : ∀ offset ∈ offsets, offset < step)
    (indexAligned : index % 8 = 0) (stepAligned : step % 8 = 0)
    (offsetAligned : ∀ offset ∈ offsets, offset % 8 = 0)
    (reads : ∀ offset, index ≤ offset → offset < index + step * rounds → offset % 8 = 0 →
      region (byteAddress src offset)) :
    Agree region (memoryWalk left src dst index step offsets rounds)
      (memoryWalk right src dst index step offsets rounds) := by
  induction rounds generalizing left right index with
  | zero => exact same
  | succ rounds ih =>
    have next := memoryMany_agrees region left right same src dst (BitVec.ofNat 64 index) offsets (by
      intro offset member
      have cell := reads (index + offset) (by omega) (by
        have := bounded offset member
        simp only [Nat.mul_succ]
        omega) (by simp [Nat.add_mod, indexAligned, offsetAligned offset member])
      simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using cell)
    exact ih _ _ next (index + step) (by simp [Nat.add_mod, indexAligned, stepAligned]) (by
      intro offset low high aligned
      apply reads offset (by omega) ?_ aligned
      simp only [Nat.mul_succ]
      omega)

end InitECandidate.Solver.WitnessRadix.CopyWords

#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.memoryMany_agrees
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.memoryWalk_agrees
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.memoryMany_agrees
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.memoryWalk_agrees
