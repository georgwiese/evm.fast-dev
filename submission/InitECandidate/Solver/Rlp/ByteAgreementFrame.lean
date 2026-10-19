import InitECandidate.Solver.Rlp.ScratchBytes
import InitECandidate.Solver.Rlp.ReadLengthUnique

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact

/-- Actual scratch word preservation implies agreement on the selected
input byte span, including unaligned pointers and either endian. -/
theorem Above.bytes_agree (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat)
    (pointer length : BitVec 64) (frame : Above source target cutoff)
    (aligned : cutoff%8=0) (below : cutoff≤pointer.toNat) (fits : pointer.toNat+length.toNat<2^64)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) :
    ReadLength.BytesAgree source target pointer length := by
  intro offset inside
  have number : (pointer+offset).toNat=pointer.toNat+offset.toNat := BitVec.toNat_add_of_lt (by omega)
  have read := Above.read_byte source target cutoff (pointer+offset) frame aligned (by rw [number]; omega) domain endian
  exact read.symm

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.Above.bytes_agree
