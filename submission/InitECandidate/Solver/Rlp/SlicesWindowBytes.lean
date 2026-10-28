import InitECandidate.Solver.Rlp.SliceArrayModel

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack PanSemStateFiniteExact

theorem Window.bytes_before (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (lower upper : Nat) (pointer length : BitVec 64) (frame : Window source target lower upper)
    (before : pointer.toNat+length.toNat≤lower) (fits : pointer.toNat+length.toNat<2^64)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) :
    ReadLength.BytesAgree source target pointer length := by
  intro offset inside
  have number : (pointer+offset).toNat=pointer.toNat+offset.toNat := BitVec.toNat_add_of_lt (by omega)
  have backing := WitnessRadix.AllocatedBytes.aligned_number (pointer+offset)
  have memory := frame (panByteAlignHOL (width:=64) (pointer+offset)) (Or.inl (by rw [backing,number]; omega))
  by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) (pointer+offset))
  all_goals simp [ReadLength.byte,panMemLoadByteHOL,memory,domain,endian,mapped]

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.Window.bytes_before
