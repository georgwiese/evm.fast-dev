import InitECandidate.Solver.Rlp.ReadLengthUnique
import InitECandidate.Solver.Input.BlobBytes
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack PanSemStateFiniteExact

/-- The combined actual scratch/array footprint retains the complete
copied input, not just the header bytes used by the current parser. -/
theorem copied_input_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (inputBase : BitVec 64) (cutoff lower upper : Nat)
    (copied : Input.Blob.HeapInput source input inputBase) (aligned : inputBase.toNat%8=0)
    (beyond : cutoff≤inputBase.toNat) (before : inputBase.toNat+input.length%2^64≤lower) (small : lower<2^64)
    (frame : ∀ query : BitVec 64,cutoff≤query.toNat → query.toNat<lower ∨ upper≤query.toNat → target.memory query=source.memory query)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) : Input.Blob.HeapInput target input inputBase := by
  intro offset inside
  let address := inputBase+BitVec.ofNat 64 offset
  have number : address.toNat=inputBase.toNat+offset := WitnessRadix.MemoryBytes.offset_toNat inputBase offset (by omega)
  have backing := WitnessRadix.AllocatedBytes.aligned_number address
  have memory := frame (panByteAlignHOL (width:=64) address) (by rw [backing,number]; omega) (Or.inl (by rw [backing,number]; omega))
  have preserved : ReadLength.byte target address=ReadLength.byte source address := by
    by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) address)
    all_goals simp [ReadLength.byte,panMemLoadByteHOL,domain,endian,memory,mapped]
  change ReadLength.byte target address=_
  rw [preserved]
  exact copied offset inside

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.copied_input_frame
