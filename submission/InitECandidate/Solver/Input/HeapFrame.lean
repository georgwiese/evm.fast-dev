import InitECandidate.Solver.Input.BlobBytes
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input.Blob
open Flapjack PanSemStateFiniteExact

/-- Copy-byte correspondence depends only on actual memory, domain and endian. -/
theorem HeapInput.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer : BitVec 64)
    (memory : source.memory=target.memory) (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (heap : HeapInput source input pointer) : HeapInput target input pointer := by
  intro offset inside
  rw [←WitnessRadix.MemoryBytes.read_of_fields source target memory domain endian]
  exact heap offset inside

theorem HeapInput.store_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer address value : BitVec 64) (heap : HeapInput source input pointer)
    (away : ∀ offset<input.length%2^64,panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 offset)≠address) :
    HeapInput {source with memory:=WitnessRadix.StoreWord.put source.memory address value} input pointer := by
  intro offset inside
  rw [WitnessRadix.StoreWord.byte_away source address value _ (away offset inside)]
  exact heap offset inside

/-- Stores to words before or after the copied input extent preserve every
input byte used by the decoder. Only natural allocation geometry is assumed. -/
theorem HeapInput.store_separate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer address value : BitVec 64) (heap : HeapInput source input pointer)
    (aligned : pointer.toNat%8=0) (fits : pointer.toNat+input.length%2^64<2^64)
    (separate : address.toNat<pointer.toNat ∨ pointer.toNat+input.length%2^64≤address.toNat) :
    HeapInput {source with memory:=WitnessRadix.StoreWord.put source.memory address value} input pointer := by
  apply HeapInput.store_away source input pointer address value heap
  intro offset inside same
  have number:=WitnessRadix.MemoryBytes.offset_toNat pointer offset (by omega)
  have cellNumber:=WitnessRadix.AllocatedBytes.aligned_number (pointer+BitVec.ofNat 64 offset)
  have equal:=congrArg BitVec.toNat same
  rw [cellNumber,number] at equal
  rcases separate with before|after
  · omega
  · omega

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.HeapInput.of_fields
#print axioms InitECandidate.Solver.Input.Blob.HeapInput.store_away
#print axioms InitECandidate.Solver.Input.Blob.HeapInput.store_separate
