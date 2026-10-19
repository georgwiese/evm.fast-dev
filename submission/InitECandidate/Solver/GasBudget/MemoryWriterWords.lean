import InitECandidate.Solver.GasBudget.MemoryWriterBytes
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.GasBudget.MemoryWriter
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem word_key (pointer : BitVec 64) (offset : Nat) (aligned : pointer.toNat % 8 = 0)
    (offsetAligned : offset % 8 = 0) (small : offset < 32) :
    panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 offset) = pointer + BitVec.ofNat 64 offset := by
  have offsetNumber : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have number := BitVec.toNat_add pointer (BitVec.ofNat 64 offset)
  rw [offsetNumber] at number
  have pointerDivision := Nat.mod_add_div pointer.toNat 8
  have offsetDivision := Nat.mod_add_div offset 8
  have sumDivision := Nat.mod_add_div (pointer.toNat + offset) 18446744073709551616
  have resultDivision := Nat.mod_add_div (pointer + BitVec.ofNat 64 offset).toNat 8
  have remainder : (pointer + BitVec.ofNat 64 offset).toNat % 8 = 0 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [AllocatedBytes.aligned_number]
  omega

theorem word_mapped {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer : BitVec 64}
    (mapped : BytesMapped source pointer 32) (aligned : pointer.toNat % 8 = 0) (offset : Nat)
    (offsetAligned : offset % 8 = 0) (small : offset < 32) : source.memaddrs (pointer + BitVec.ofNat 64 offset) := by
  have current := mapped offset small
  rw [word_key pointer offset aligned offsetAligned small] at current
  exact current

theorem word_away {pointer query : BitVec 64} (away : BytesAway pointer query 32) (aligned : pointer.toNat % 8 = 0)
    (offset : Nat) (offsetAligned : offset % 8 = 0) (small : offset < 32) : query ≠ pointer + BitVec.ofNat 64 offset := by
  have current := away offset small
  rw [word_key pointer offset aligned offsetAligned small] at current
  exact current

end InitECandidate.Solver.GasBudget.MemoryWriter

#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.word_key
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.word_mapped
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.word_away
