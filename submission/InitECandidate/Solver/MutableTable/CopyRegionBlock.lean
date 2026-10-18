import InitECandidate.Solver.MutableTable.CopyWordContents
import InitECandidate.Solver.MutableTable.MemoryRegionSeparation

namespace InitECandidate.Solver.MutableTable.CopyContents
open Flapjack WitnessRadix

theorem indexed_byte (pointer : BitVec 64) (index offset : Nat) :
    pointer + BitVec.ofNat 64 index + BitVec.ofNat 64 offset = byteAddress pointer (index + offset) := by
  simp only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc]

theorem block_preserves_source (input : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (index : Nat) (offsets : List Nat) (inside : ∀ offset ∈ offsets, index + offset < dst.length)
    (query : Nat) (queryInside : query < src.length) :
    CopyWords.memoryMany input (MemoryRegion.pointer src) (MemoryRegion.pointer dst) (BitVec.ofNat 64 index) offsets (byteAddress (MemoryRegion.pointer src) query) =
      input (byteAddress (MemoryRegion.pointer src) query) := by
  apply CopyWords.memoryMany_away
  intro offset member
  rw [indexed_byte]
  exact MemoryRegion.separate src dst srcValid dstValid apart query (index + offset) queryInside (inside offset member)

/-- Actual original four-word or one-word copy block contents at every
selected destination, specialized from the general separated-store lemma. -/
theorem block_at (input snapshot : WordWrites.Memory) (src dst : MemoryRegion.Region)
    (srcValid : MemoryRegion.Valid src) (dstValid : MemoryRegion.Valid dst)
    (apart : src.start + src.length ≤ dst.start ∨ dst.start + dst.length ≤ src.start)
    (index : Nat) (offsets : List Nat)
    (sourceInside : ∀ offset ∈ offsets, index + offset < src.length) (destinationInside : ∀ offset ∈ offsets, index + offset < dst.length)
    (sourceKept : ∀ offset < src.length, input (byteAddress (MemoryRegion.pointer src) offset) = snapshot (byteAddress (MemoryRegion.pointer src) offset))
    (query : Nat) (member : query ∈ offsets) :
    CopyWords.memoryMany input (MemoryRegion.pointer src) (MemoryRegion.pointer dst) (BitVec.ofNat 64 index) offsets (byteAddress (MemoryRegion.pointer dst) (index + query)) =
      snapshot (byteAddress (MemoryRegion.pointer src) (index + query)) := by
  have copied := memory_many_at input snapshot (MemoryRegion.pointer src) (MemoryRegion.pointer dst) (BitVec.ofNat 64 index) offsets
    (by intro offset belongs; rw [indexed_byte]; exact sourceKept _ (sourceInside offset belongs))
    (by intro first firstMember second secondMember; rw [indexed_byte, indexed_byte]; exact MemoryRegion.separate src dst srcValid dstValid apart _ _ (sourceInside first firstMember) (destinationInside second secondMember))
    (by
      intro first firstMember second secondMember same
      rw [indexed_byte, indexed_byte] at same
      have numeric := MemoryRegion.byte_address_injective dst dstValid (index + first) (index + second) (by have := destinationInside first firstMember; omega) (by have := destinationInside second secondMember; omega) same
      omega) query member
  simpa only [indexed_byte] using copied

end InitECandidate.Solver.MutableTable.CopyContents

#print axioms InitECandidate.Solver.MutableTable.CopyContents.indexed_byte
#print axioms InitECandidate.Solver.MutableTable.CopyContents.block_preserves_source
#print axioms InitECandidate.Solver.MutableTable.CopyContents.block_at
