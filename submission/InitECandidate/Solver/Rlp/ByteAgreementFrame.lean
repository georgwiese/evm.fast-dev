import InitECandidate.Solver.Rlp.ValidationWriteFrame
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.Rlp.ReadLengthUnique

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

/-- The actual scratch footprint preserves byte reads below its frame cursor,
including unaligned addresses and either endian. Runtime fields are retained. -/
theorem Outside.read_byte_below (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (lower upper : Nat) (address : BitVec 64) (frame : Outside source target lower upper)
    (before : address.toNat < lower) :
    @panMemLoadByteHOL 64 _ target.memory target.memaddrs (fun query=>Classical.propDecidable (target.memaddrs query)) target.be address=
      @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun query=>Classical.propDecidable (source.memaddrs query)) source.be address := by
  have number := WitnessRadix.AllocatedBytes.aligned_number address
  have backing : (panByteAlignHOL (width:=64) address).toNat < lower := by rw [number]; omega
  have memory := frame (panByteAlignHOL (width:=64) address) (Or.inl backing)
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame.runtime
  have endian := congrArg PanSemStateFiniteExact.be frame.runtime
  change target.memaddrs=source.memaddrs at domain
  change target.be=source.be at endian
  by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) address)
  all_goals simp [panMemLoadByteHOL,domain,endian,memory,mapped]

end InitECandidate.Solver.Rlp.Validation

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

/-- Input spans owned below the frame cursor retain precisely their byte
observations through real scratch writes; no whole-memory equality is needed. -/
theorem Outside.bytes_agree_below (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (lower upper : Nat) (pointer length : BitVec 64) (frame : Outside source target lower upper)
    (fits : pointer.toNat+length.toNat<2^64) (before : pointer.toNat+length.toNat≤lower) :
    ReadLength.BytesAgree source target pointer length := by
  intro offset inside
  have number : (pointer+offset).toNat=pointer.toNat+offset.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  exact (Outside.read_byte_below source target lower upper (pointer+offset) frame (by rw [number]; omega)).symm

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.Above.bytes_agree

#print axioms InitECandidate.Solver.Rlp.Validation.Outside.bytes_agree_below

#print axioms InitECandidate.Solver.Rlp.Validation.Above.mono
#print axioms InitECandidate.Solver.Rlp.Validation.Above.read_byte
#print axioms InitECandidate.Solver.Rlp.Validation.Outside.read_byte_below
