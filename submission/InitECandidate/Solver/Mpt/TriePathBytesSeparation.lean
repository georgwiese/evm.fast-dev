import InitECandidate.Solver.Mpt.TriePathBytes

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A path ending before a node cannot share any of that node's cells,
even when the last path byte uses an unaligned backing word. -/
theorem NibbleSpan.apart_before (memory : Memory) (domain : BitVec 64→Prop) (be : Bool)
    (pointer owner : BitVec 64) (length size : Nat) (span : NibbleSpan memory domain be pointer length)
    (arena : AllocatedBytes.Arena owner size) (before : pointer.toNat+length≤owner.toNat)
    (index : Nat) (inside : index<length) (offset : Nat) (within : offset<size) :
    panByteAlignHOL (width:=64) (byteAddress pointer index)≠byteAddress owner offset := by
  intro same
  have number:=byteAddress_toNat pointer index (by have fits:=span.fits; omega)
  have ownerNumber:=byteAddress_toNat owner offset (by have upper:=arena.upper; omega)
  have equal:=congrArg BitVec.toNat same
  rw [AllocatedBytes.aligned_number,number,ownerNumber] at equal
  omega

/-- A freshly aligned path starts after every cell of an older node.
Its first backing word therefore cannot alias the older allocation. -/
theorem NibbleSpan.apart_after (memory : Memory) (domain : BitVec 64→Prop) (be : Bool)
    (pointer owner : BitVec 64) (length size : Nat) (span : NibbleSpan memory domain be pointer length)
    (aligned : pointer.toNat%8=0) (arena : AllocatedBytes.Arena owner size)
    (before : owner.toNat+size≤pointer.toNat)
    (index : Nat) (inside : index<length) (offset : Nat) (within : offset<size) :
    panByteAlignHOL (width:=64) (byteAddress pointer index)≠byteAddress owner offset := by
  intro same
  have number:=byteAddress_toNat pointer index (by have fits:=span.fits; omega)
  have ownerNumber:=byteAddress_toNat owner offset (by have upper:=arena.upper; omega)
  have equal:=congrArg BitVec.toNat same
  rw [AllocatedBytes.aligned_number,number,ownerNumber] at equal
  omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.apart_before
#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.apart_after
