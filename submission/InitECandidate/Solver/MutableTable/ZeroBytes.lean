import InitECandidate.Solver.MutableTable.ByteStore
import InitECandidate.Solver.MutableTable.ZeroWords
import InitECandidate.Solver.WitnessRadix.ZeroByteState

namespace InitECandidate.Solver.MutableTable.ZeroBytes
open Flapjack WitnessRadix

def read (memory : WordWrites.Memory) (address : BitVec 64) : UInt8 :=
  panGetByteHOL address (MemoryBytes.wordBits (memory (panByteAlignHOL (width:=64) address))) false

theorem byteMemory_read (memory : WordWrites.Memory) (address query : BitVec 64) :
    read (Zero.byteMemory memory false address) query=if query=address then 0 else read memory query := by
  exact ByteStore.projection memory address query 0

theorem memoryByte_preserves (memory : WordWrites.Memory) (dst query : BitVec 64) (index blocks : Nat)
    (old : read memory query=0) : read (Zero.memoryByte memory false dst index blocks) query=0 := by
  induction blocks generalizing memory index with
  | zero=>exact old
  | succ blocks ih=>
    apply ih
    rw [byteMemory_read]
    split <;> simp_all

theorem memoryByte_cell (memory : WordWrites.Memory) (dst : BitVec 64) (index blocks slot : Nat)
    (inside : slot<blocks) :
    read (Zero.memoryByte memory false dst index blocks) (dst+BitVec.ofNat 64 (index+slot))=0 := by
  induction blocks generalizing memory index slot with
  | zero=>omega
  | succ blocks ih=>
    rw [Zero.memoryByte]
    cases slot with
    | zero=>apply memoryByte_preserves;simp [byteMemory_read]
    | succ slot=>
      have arithmetic : index+(slot+1)=index+1+slot:=by omega
      rw [arithmetic]
      exact ih _ (index+1) slot (by omega)

theorem aligned_offset (dst : BitVec 64) (offset : Nat) (aligned : dst.toNat%8=0)
    (fits : dst.toNat+offset<2^64) :
    panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 offset)=dst+BitVec.ofNat 64 (8*(offset/8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [ByteStore.aligned_number,MemoryBytes.offset_toNat dst offset fits,
    MemoryBytes.offset_toNat dst (8*(offset/8)) (by omega)]
  omega

/-- All bytes of the actual aligned clearing pass read back zero. -/
theorem final_byte (memory : WordWrites.Memory) (dst : BitVec 64) (length offset : Nat)
    (multiple : length%8=0) (inside : offset<length) (aligned : dst.toNat%8=0)
    (fits : dst.toNat+length<2^64) :
    read (Zero.finalMemory memory dst length) (dst+BitVec.ofNat 64 offset)=0 := by
  have stored:=ZeroWords.final_cell memory dst length (offset/8) (by omega)
  unfold read
  rw [aligned_offset dst offset aligned (by omega),stored]
  simp [MemoryBytes.wordBits,panGetByteHOL]

end InitECandidate.Solver.MutableTable.ZeroBytes

#print axioms InitECandidate.Solver.MutableTable.ZeroBytes.memoryByte_cell
#print axioms InitECandidate.Solver.MutableTable.ZeroBytes.final_byte
