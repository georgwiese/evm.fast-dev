import InitECandidate.Solver.Rlp.ByteAgreementFrame
import InitECandidate.Solver.Input.BlobBytes


namespace InitECandidate.Solver.Input.Blob
open Flapjack PanSemStateFiniteExact

/-- Transport the actual copied input bytes through an established scratch
footprint. The encoded extent remains input.length modulo2^64. -/
theorem HeapInput.above (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (cutoff : Nat) (heap : HeapInput source input pointer)
    (frame : Rlp.Validation.Above source target cutoff) (aligned : cutoff%8=0) (upper : cutoff≤pointer.toNat)
    (fits : pointer.toNat+input.length%2^64<2^64)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) : HeapInput target input pointer := by
  intro offset inside
  have number := WitnessRadix.MemoryBytes.offset_toNat pointer offset (by omega)
  rw [Rlp.Validation.Above.read_byte source target cutoff (pointer+BitVec.ofNat 64 offset) frame aligned (by rw [number]; omega) domain endian]
  exact heap offset inside

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.HeapInput.above
