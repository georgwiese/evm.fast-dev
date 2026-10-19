import InitECandidate.Solver.Rlp.SlicesStores
import InitECandidate.Solver.Rlp.ReadLengthUnique
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack PanSemStateFiniteExact

theorem row_number (array index : BitVec 64) (fits : array.toNat+16*index.toNat<2^64) :
    (row array index).toNat=array.toNat+16*index.toNat := by
  have product : (index*16#64).toNat=16*index.toNat := by
    rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by change index.toNat*16<2^64; omega)]
    change index.toNat*16=16*index.toNat
    omega
  rw [row,BitVec.toNat_add_of_lt (by rw [product]; exact fits),product]

theorem row_length_number (array index count : BitVec 64) (inside : index.toNat<count.toNat)
    (fits : array.toNat+16*count.toNat<2^64) :
    (row array index+8#64).toNat=array.toNat+16*index.toNat+8 := by
  have number := row_number array index (by omega)
  rw [BitVec.toNat_add_of_lt (by rw [number]; change array.toNat+16*index.toNat+8<2^64; omega),number]
  rfl

theorem written_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array index offset size query : BitVec 64)
    (first : query≠row array index) (second : query≠row array index+8#64) :
    (written source pointer array index offset size).memory query=source.memory query := by
  simp only [written,WitnessRadix.StoreWord.put,if_neg first,if_neg second]

theorem written_head (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array index offset size : BitVec 64)
    (separate : row array index≠row array index+8#64) :
    (written source pointer array index offset size).memory (row array index)=.word (pointer+offset) ∧
      (written source pointer array index offset size).memory (row array index+8#64)=.word size := by
  simp [written,WitnessRadix.StoreWord.put,separate]

/-- Both real array stores are above the entire original input span, so
every actual input byte is retained, including unaligned sub-items. -/
theorem stores_input_bytes (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length array index count offset size : BitVec 64)
    (before : pointer.toNat+length.toNat≤array.toNat) (inside : index.toNat<count.toNat)
    (fits : array.toNat+16*count.toNat<2^64) :
    ReadLength.BytesAgree source (storesPost source pointer array index offset size) pointer length := by
  have firstNumber := row_number array index (by omega)
  have secondNumber := row_length_number array index count inside fits
  intro byteOffset bounded
  have inputNumber : (pointer+byteOffset).toNat=pointer.toNat+byteOffset.toNat := BitVec.toNat_add_of_lt (by omega)
  have backingNumber := WitnessRadix.AllocatedBytes.aligned_number (pointer+byteOffset)
  have firstAway : panByteAlignHOL (width:=64) (pointer+byteOffset)≠row array index := by
    intro same
    have number := congrArg BitVec.toNat same
    rw [firstNumber,backingNumber,inputNumber] at number
    omega
  have secondAway : panByteAlignHOL (width:=64) (pointer+byteOffset)≠row array index+8#64 := by
    intro same
    have number := congrArg BitVec.toNat same
    rw [secondNumber,backingNumber,inputNumber] at number
    omega
  have memory := written_away source pointer array index offset size (panByteAlignHOL (width:=64) (pointer+byteOffset)) firstAway secondAway
  change ReadLength.byte source (pointer+byteOffset)=ReadLength.byte (written source pointer array index offset size) (pointer+byteOffset)
  simp only [ReadLength.byte,panMemLoadByteHOL,memory]
  rfl

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.row_number
#print axioms InitECandidate.Solver.Rlp.Slices.row_length_number
#print axioms InitECandidate.Solver.Rlp.Slices.written_away
#print axioms InitECandidate.Solver.Rlp.Slices.written_head
#print axioms InitECandidate.Solver.Rlp.Slices.stores_input_bytes
