import InitECandidate.Solver.MutableTable.CopyRegionWalk

namespace InitECandidate.Solver.MutableTable.CopyContents
open Flapjack WitnessRadix

theorem regions_aligned (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst) :
    CopyGeneral.aligned (MemoryRegion.pointer src) (MemoryRegion.pointer dst) := by
  unfold CopyGeneral.aligned
  rw [BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff]
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [WordBits.mask7, MemoryRegion.pointer_number dst dstValid, dstValid.aligned]
    rfl
  · apply BitVec.eq_of_toNat_eq
    rw [WordBits.mask7, MemoryRegion.pointer_number src srcValid, srcValid.aligned]
    rfl

theorem prefix_index_word_multiple (length : Nat) (multiple : length % 8 = 0) :
    CopyWords.prefixIndex length = length := by
  unfold CopyWords.prefixIndex
  omega

/-- The unchanged memcpy's aligned word prefix copies every full-word
position from a disjoint source region. -/
theorem prefix_at (input : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (length : Nat) (srcRoom : length ≤ src.length) (dstRoom : length ≤ dst.length)
    (multiple : length % 8 = 0) (query : Nat) (inside : query < length) (aligned : query % 8 = 0) :
    CopyGeneral.prefixMemory input (MemoryRegion.pointer src) (MemoryRegion.pointer dst) length
      (byteAddress (MemoryRegion.pointer dst) query) = input (byteAddress (MemoryRegion.pointer src) query) := by
  have total := prefix_index_word_multiple length multiple
  unfold CopyWords.prefixIndex at total
  have offsetBound : ∀ offset ∈ CopyWords.wordOffsets, offset < 32 := by
    intro offset member
    simp [CopyWords.wordOffsets] at member
    omega
  have zeroBound : ∀ offset ∈ ([0] : List Nat), offset < 8 := by simp
  let first := CopyWords.memoryWalk input (MemoryRegion.pointer src) (MemoryRegion.pointer dst) 0 32 CopyWords.wordOffsets (length / 32)
  have firstSource : ∀ offset < src.length, first (byteAddress (MemoryRegion.pointer src) offset) = input (byteAddress (MemoryRegion.pointer src) offset) := by
    intro offset offsetInside
    exact walk_preserves_source input src dst srcValid dstValid apart 0 32 CopyWords.wordOffsets (length / 32) offsetBound (by omega) offset offsetInside
  unfold CopyGeneral.prefixMemory
  change CopyWords.memoryWalk first (MemoryRegion.pointer src) (MemoryRegion.pointer dst) (32 * (length / 32)) 8 [0] ((length % 32) / 8) _ = _
  by_cases early : query < 32 * (length / 32)
  · have copied := walk_at input input src dst srcValid dstValid apart 0 32 CopyWords.wordOffsets (length / 32) offsetBound
      (by omega) (by omega) (by intro offset h; rfl) (query / 32) (by omega) (query % 32) (by
        simp [CopyWords.wordOffsets]
        omega)
    have indexEq : 0 + 32 * (query / 32) + query % 32 = query := by omega
    rw [indexEq] at copied
    have preserved : CopyWords.memoryWalk first (MemoryRegion.pointer src) (MemoryRegion.pointer dst) (32 * (length / 32)) 8 [0] ((length % 32) / 8)
        (byteAddress (MemoryRegion.pointer dst) query) = first (byteAddress (MemoryRegion.pointer dst) query) := by
      apply CopyWords.memoryWalk_away _ _ _ _ _ _ _ _ zeroBound
      intro offset lower upper same
      have equal := MemoryRegion.byte_address_injective dst dstValid query offset (by omega) (by omega) same
      omega
    exact preserved.trans copied
  · have indexEq : 32 * (length / 32) + 8 * ((query - 32 * (length / 32)) / 8) + 0 = query := by omega
    have copied := walk_at first input src dst srcValid dstValid apart (32 * (length / 32)) 8 [0] ((length % 32) / 8) zeroBound
      (by omega) (by omega) firstSource ((query - 32 * (length / 32)) / 8) (by omega) 0 (by simp)
    rw [indexEq] at copied
    exact copied

theorem word_at (input : WordWrites.Memory) (be : Bool) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (length : Nat) (srcRoom : length ≤ src.length) (dstRoom : length ≤ dst.length)
    (multiple : length % 8 = 0) (query : Nat) (inside : query < length) (aligned : query % 8 = 0) :
    CopyGeneral.resultMemory input be (MemoryRegion.pointer src) (MemoryRegion.pointer dst) length
      (byteAddress (MemoryRegion.pointer dst) query) = input (byteAddress (MemoryRegion.pointer src) query) := by
  rw [CopyGeneral.resultMemory, if_pos (regions_aligned src dst srcValid dstValid), prefix_index_word_multiple length multiple]
  simp only [CopyGeneral.suffixMemory, Nat.sub_self, Nat.zero_div, Nat.zero_mod, CopyBytes.memoryWalk]
  exact prefix_at input src dst srcValid dstValid apart length srcRoom dstRoom multiple query inside aligned

end InitECandidate.Solver.MutableTable.CopyContents

#print axioms InitECandidate.Solver.MutableTable.CopyContents.regions_aligned
#print axioms InitECandidate.Solver.MutableTable.CopyContents.prefix_index_word_multiple
#print axioms InitECandidate.Solver.MutableTable.CopyContents.prefix_at
#print axioms InitECandidate.Solver.MutableTable.CopyContents.word_at
