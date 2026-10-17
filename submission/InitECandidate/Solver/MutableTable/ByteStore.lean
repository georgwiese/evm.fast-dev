import InitECandidate.Solver.MutableTable.FindModel32

namespace InitECandidate.Solver.MutableTable.ByteStore
open Flapjack PanSemStateFiniteExact
open WitnessRadix

def write (memory : WordWrites.Memory) (address : BitVec 64) (byte : UInt8) : WordWrites.Memory :=
  StoreWord.put memory (panByteAlignHOL (width:=64) address)
    (panSetByteHOL address (BitVec.ofNat 64 byte.toNat)
      (MemoryBytes.wordBits (memory (panByteAlignHOL (width:=64) address))) false)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- Exact projection of a little-endian byte replacement, including the
other seven bytes of the same physical word. -/
theorem get_set (address query cell : BitVec 64) (byte : UInt8) :
    panGetByteHOL query (panSetByteHOL address (BitVec.ofNat 64 byte.toNat) cell false) false =
      if query.toNat%8=address.toNat%8 then byte else panGetByteHOL query cell false := by
  apply UInt8.toNat.inj
  have written:=panSetByteHOL_toNat (width:=64) (by decide) address cell byte false
  have byteBound : byte.toNat<256:=byte.toNat_lt_size
  have cellBound : cell.toNat<2^64:=cell.isLt
  simp only [byteBitIndex,Bool.false_eq_true,if_false] at written
  simp only [panGetByteHOL,Bool.false_eq_true,if_false,UInt8.toNat_ofNat',Nat.mod_mod]
  rw [written]
  have wBound : address.toNat%8<8:=Nat.mod_lt _ (by decide)
  have rBound : query.toNat%8<8:=Nat.mod_lt _ (by decide)
  generalize address.toNat%8=w at *
  generalize query.toNat%8=r at *
  interval_cases w <;> interval_cases r <;>
    simp_all only [Nat.reduceMul,Nat.reduceAdd,Nat.reducePow,
      Nat.reduceEqDiff,ite_true,ite_false,UInt8.toNat_ofNat',Nat.mod_mod] <;> omega

theorem aligned_number (address : BitVec 64) :
    (panByteAlignHOL (width:=64) address).toNat=address.toNat/8*8 := by
  change (BitVec.ofNat 64 (address.toNat/8*8)).toNat=_
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := address.isLt;omega)]

/-- Byte replacement preserves all other bytes, even in the same word. -/
theorem projection (memory : WordWrites.Memory) (address query : BitVec 64) (byte : UInt8) :
    panGetByteHOL query (MemoryBytes.wordBits (write memory address byte (panByteAlignHOL (width:=64) query))) false=
      if query=address then byte else
        panGetByteHOL query (MemoryBytes.wordBits (memory (panByteAlignHOL (width:=64) query))) false := by
  by_cases same : query=address
  · subst query
    simp [write,StoreWord.put,MemoryBytes.wordBits,get_set]
  · by_cases sameCell : panByteAlignHOL (width:=64) query=panByteAlignHOL (width:=64) address
    · have different : query.toNat%8≠address.toNat%8 := by
        intro equal
        have numbers:=congrArg BitVec.toNat sameCell
        rw [aligned_number,aligned_number] at numbers
        apply same
        apply BitVec.eq_of_toNat_eq
        omega
      simp only [write,StoreWord.put,if_pos sameCell,MemoryBytes.wordBits,get_set,if_neg different,if_neg same]
      rw [sameCell]
    · simp [write,StoreWord.put,sameCell,same]

/-- The actual byte-load helper after replacement, with its mapped-cell test. -/
theorem read_write {F : Type} (source : PanSemStateFiniteExact 64 F)
    (address query : BitVec 64) (byte : UInt8) (little : source.be=false)
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) address)) :
    @panMemLoadByteHOL 64 _ (write source.memory address byte) source.memaddrs
      (fun pointer=>Classical.propDecidable (source.memaddrs pointer)) source.be query=
      if query=address then some byte else
        @panMemLoadByteHOL 64 _ source.memory source.memaddrs
          (fun pointer=>Classical.propDecidable (source.memaddrs pointer)) source.be query := by
  classical
  have load (memory : WordWrites.Memory) :
      @panMemLoadByteHOL 64 _ memory source.memaddrs
        (fun pointer=>Classical.propDecidable (source.memaddrs pointer)) source.be query=
      if source.memaddrs (panByteAlignHOL (width:=64) query) then
        some (panGetByteHOL query (MemoryBytes.wordBits (memory (panByteAlignHOL (width:=64) query))) false) else none := by
    cases stored : memory (panByteAlignHOL (width:=64) query)
    simp only [panMemLoadByteHOL,stored,MemoryBytes.wordBits,little]
  rw [load,load,projection]
  by_cases same : query=address
  · subst query;simp [mapped]
  · simp [same]

end InitECandidate.Solver.MutableTable.ByteStore

#print axioms InitECandidate.Solver.MutableTable.ByteStore.get_set
#print axioms InitECandidate.Solver.MutableTable.ByteStore.projection
#print axioms InitECandidate.Solver.MutableTable.ByteStore.read_write
