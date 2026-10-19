import InitECandidate.Solver.Rlp.ValidationWriteFrame
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.Input.BlobBytes

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact

theorem Above.mono (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (frame : Above source target lower) (ordered : lower≤upper) : Above source target upper :=
  fun query beyond=>frame query (ordered.trans beyond)

/-- A word footprint above an aligned boundary preserves each actual byte
read there, with arbitrary byte alignment and either endian. -/
theorem Above.read_byte (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat) (address : BitVec 64)
    (frame : Above source target cutoff) (aligned : cutoff%8=0) (upper : cutoff≤address.toNat)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) :
    @panMemLoadByteHOL 64 _ target.memory target.memaddrs (fun query=>Classical.propDecidable (target.memaddrs query)) target.be address=
      @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun query=>Classical.propDecidable (source.memaddrs query)) source.be address := by
  have number := WitnessRadix.AllocatedBytes.aligned_number address
  have backing : cutoff≤(panByteAlignHOL (width:=64) address).toNat := by rw [number]; omega
  have memory := frame (panByteAlignHOL (width:=64) address) backing
  by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) address)
  all_goals simp [panMemLoadByteHOL,domain,endian,memory,mapped]

end InitECandidate.Solver.Rlp.Validation

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

#print axioms InitECandidate.Solver.Rlp.Validation.Above.mono
#print axioms InitECandidate.Solver.Rlp.Validation.Above.read_byte
#print axioms InitECandidate.Solver.Input.Blob.HeapInput.above
