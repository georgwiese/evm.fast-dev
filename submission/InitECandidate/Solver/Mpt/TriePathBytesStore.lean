import InitECandidate.Solver.Mpt.TriePathBytes
import InitECandidate.Solver.WitnessRadix.ByteStoreRead

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A real byte store of a value below16 initializes a complete single
nibble path, including its actual read result. -/
theorem NibbleSpan.stored_byte (memory : Memory) (domain : BitVec 64 → Prop) (pointer value : BitVec 64)
    (fits : pointer.toNat+1<2^64) (small : value.toNat<16)
    (mapped : domain (panByteAlignHOL (width:=64) pointer)) :
    NibbleSpan (ByteStore.put memory false pointer (BitVec.ofNat 8 value.toNat)) domain false pointer 1 := by
  have byteNumber : (BitVec.ofNat 8 value.toNat).toNat=value.toNat:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have read:=ByteStore.read_self memory domain pointer (BitVec.ofNat 8 value.toNat) mapped
  rw [byteNumber] at read
  refine ⟨fits,?_,?_⟩
  · intro offset inside
    have zero : offset=0:=by omega
    simpa only [zero,byteAddress,BitVec.add_zero] using mapped
  · intro offset inside
    have zero : offset=0:=by omega
    refine ⟨UInt8.ofNat value.toNat,?_,?_⟩
    · rw [UInt8.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]; exact small
    · simpa only [zero,byteAddress,BitVec.add_zero] using read

/-- An aligned fresh byte store leaves every raw word before its actual
allocation frontier unchanged, for either byte order. -/
theorem byte_store_before (memory : Memory) (be : Bool) (pointer query : BitVec 64) (value : BitVec 8)
    (aligned : pointer.toNat%8=0) (before : query.toNat<pointer.toNat) :
    ByteStore.put memory be pointer value query=memory query := by
  apply ByteStore.away
  intro same
  have number:=congrArg BitVec.toNat same
  rw [AllocatedBytes.aligned_number] at number
  omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.stored_byte
#print axioms InitECandidate.Solver.Mpt.TrieWalk.byte_store_before
