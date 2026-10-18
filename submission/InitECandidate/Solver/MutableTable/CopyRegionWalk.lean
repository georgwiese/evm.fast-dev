import InitECandidate.Solver.MutableTable.CopyRegionBlock

namespace InitECandidate.Solver.MutableTable.CopyContents
open Flapjack WitnessRadix

theorem walk_preserves_source (input : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (index step : Nat) (offsets : List Nat) (rounds : Nat) (offsetBound : ∀ offset ∈ offsets, offset < step)
    (full : index + step * rounds ≤ dst.length) (query : Nat) (inside : query < src.length) :
    CopyWords.memoryWalk input (MemoryRegion.pointer src) (MemoryRegion.pointer dst) index step offsets rounds (byteAddress (MemoryRegion.pointer src) query) =
      input (byteAddress (MemoryRegion.pointer src) query) := by
  apply CopyWords.memoryWalk_away _ _ _ _ _ _ _ _ offsetBound
  intro offset lower upper
  exact MemoryRegion.separate src dst srcValid dstValid apart query offset inside (by omega)

/-- The original aligned memcpy word loops reproduce every selected source
word, with explicit region separation and destination injectivity. -/
theorem walk_at (input snapshot : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (index step : Nat) (offsets : List Nat) (rounds : Nat) (offsetBound : ∀ offset ∈ offsets, offset < step)
    (fullSource : index + step * rounds ≤ src.length) (fullDestination : index + step * rounds ≤ dst.length)
    (sourceKept : ∀ offset < src.length, input (byteAddress (MemoryRegion.pointer src) offset) = snapshot (byteAddress (MemoryRegion.pointer src) offset))
    (queryRound : Nat) (roundInside : queryRound < rounds) (queryOffset : Nat) (member : queryOffset ∈ offsets) :
    CopyWords.memoryWalk input (MemoryRegion.pointer src) (MemoryRegion.pointer dst) index step offsets rounds
      (byteAddress (MemoryRegion.pointer dst) (index + step * queryRound + queryOffset)) =
      snapshot (byteAddress (MemoryRegion.pointer src) (index + step * queryRound + queryOffset)) := by
  induction rounds generalizing input index queryRound with
  | zero => omega
  | succ rounds ih =>
    let block := CopyWords.memoryMany input (MemoryRegion.pointer src) (MemoryRegion.pointer dst) (BitVec.ofNat 64 index) offsets
    have firstBlock : step ≤ step * (rounds + 1) := by
      have bound := Nat.mul_le_mul_left step (show 1 ≤ rounds + 1 from by omega)
      simpa only [Nat.mul_one] using bound
    have sourceInside : ∀ offset ∈ offsets, index + offset < src.length := by
      intro offset belongs; have bound := offsetBound offset belongs; omega
    have destinationInside : ∀ offset ∈ offsets, index + offset < dst.length := by
      intro offset belongs; have bound := offsetBound offset belongs; omega
    have retained : ∀ offset < src.length, block (byteAddress (MemoryRegion.pointer src) offset) = snapshot (byteAddress (MemoryRegion.pointer src) offset) := by
      intro offset inside
      exact (block_preserves_source input src dst srcValid dstValid apart index offsets destinationInside offset inside).trans (sourceKept offset inside)
    have total : index + step + step * rounds = index + step * (rounds + 1) := by rw [Nat.mul_succ]; omega
    cases queryRound with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [CopyWords.memoryWalk]
      have untouched : CopyWords.memoryWalk block (MemoryRegion.pointer src) (MemoryRegion.pointer dst) (index + step) step offsets rounds
          (byteAddress (MemoryRegion.pointer dst) (index + queryOffset)) = block (byteAddress (MemoryRegion.pointer dst) (index + queryOffset)) := by
        apply CopyWords.memoryWalk_away _ _ _ _ _ _ _ _ offsetBound
        intro offset lower upper same
        have numeric := MemoryRegion.byte_address_injective dst dstValid (index + queryOffset) offset (by have := destinationInside queryOffset member; omega) (by rw [total] at upper; omega) same
        have bound := offsetBound queryOffset member
        omega
      rw [untouched]
      exact block_at input snapshot src dst srcValid dstValid apart index offsets sourceInside destinationInside sourceKept queryOffset member
    | succ queryRound =>
      have tail := ih block (index + step) (by rw [total]; exact fullSource) (by rw [total]; exact fullDestination) retained queryRound (by omega)
      have selected : index + step + step * queryRound + queryOffset = index + step * (queryRound + 1) + queryOffset := by rw [Nat.mul_succ]; omega
      rw [selected] at tail
      exact tail

end InitECandidate.Solver.MutableTable.CopyContents

#print axioms InitECandidate.Solver.MutableTable.CopyContents.walk_preserves_source
#print axioms InitECandidate.Solver.MutableTable.CopyContents.walk_at
