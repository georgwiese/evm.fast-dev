import InitECandidate.Solver.Mpt.TriePathBytes
import InitECandidate.Solver.WitnessRadix.CopyFullByteContent

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Relate the pure little-endian byte projection to the actual mapped
Pancake byte load; every physical memory cell is a word. -/
theorem little_byte_read (memory : Memory) (domain : BitVec 64 → Prop) (address : BitVec 64)
    (mapped : domain (panByteAlignHOL (width:=64) address)) :
    @panMemLoadByteHOL 64 _ memory domain (fun query=>Classical.propDecidable (domain query)) false address=
      some (MutableTable.CopyContents.byte memory address) := by
  cases cell : memory (panByteAlignHOL (width:=64) address) with
  | word value=>simp [panMemLoadByteHOL,MutableTable.CopyContents.byte,cell,mapped,MemoryBytes.wordBits]

theorem NibbleSpan.raw_nibble (memory : Memory) (domain : BitVec 64 → Prop) (pointer : BitVec 64) (length : Nat)
    (span : NibbleSpan memory domain false pointer length) (offset : Nat) (inside : offset<length) :
    (MutableTable.CopyContents.byte memory (byteAddress pointer offset)).toNat<16 := by
  obtain ⟨value,small,read⟩:=span.nibble offset inside
  have actual:=little_byte_read memory domain (byteAddress pointer offset) (span.mapped offset inside)
  have equal : value=MutableTable.CopyContents.byte memory (byteAddress pointer offset):=Option.some.inj (read.symm.trans actual)
  rwa [←equal]

/-- Byte agreement suffices when another unaligned copy touches the same
backing word but preserves the previous path bytes themselves. -/
theorem NibbleSpan.of_little_byte_agreement (memory nextMemory : Memory) (domain : BitVec 64 → Prop) (pointer : BitVec 64) (length : Nat)
    (span : NibbleSpan memory domain false pointer length)
    (agreement : ∀ offset<length,MutableTable.CopyContents.byte nextMemory (byteAddress pointer offset)=MutableTable.CopyContents.byte memory (byteAddress pointer offset)) :
    NibbleSpan nextMemory domain false pointer length := by
  refine ⟨span.fits,span.mapped,?_⟩
  intro offset inside
  refine ⟨MutableTable.CopyContents.byte nextMemory (byteAddress pointer offset),?_,little_byte_read nextMemory domain _ (span.mapped offset inside)⟩
  rw [agreement offset inside]
  exact span.raw_nibble memory domain pointer length offset inside

/-- The exact original memcpy output is again a full nibble buffer,
including arbitrary unaligned borrowed source/destination slices. -/
theorem NibbleSpan.copy_little (memory : Memory) (domain : BitVec 64 → Prop) (src dst : BitVec 64) (length : Nat)
    (span : NibbleSpan memory domain false src length)
    (sourceArena : AllocatedBytes.Arena src length) (destinationArena : AllocatedBytes.Arena dst length)
    (apart : src.toNat+length≤dst.toNat)
    (mapped : ∀ offset<length,domain (panByteAlignHOL (width:=64) (byteAddress dst offset))) :
    NibbleSpan (CopyGeneral.resultMemory memory false src dst length) domain false dst length := by
  refine ⟨by have upper:=destinationArena.upper; omega,mapped,?_⟩
  intro offset inside
  refine ⟨MutableTable.CopyContents.byte (CopyGeneral.resultMemory memory false src dst length) (byteAddress dst offset),?_,
    little_byte_read _ domain _ (mapped offset inside)⟩
  rw [CopyByteContent.result_byte_at memory src dst length sourceArena destinationArena apart offset inside]
  exact span.raw_nibble memory domain src length offset inside

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.little_byte_read
#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.raw_nibble
#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.of_little_byte_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.copy_little
