import InitECandidate.Solver.WitnessRadix.CopyByteRange

namespace InitECandidate.Solver.WitnessRadix.CopyByteContent
open Flapjack MutableTable.CopyContents

theorem copyMemory_shift (memory : WordWrites.Memory) (src dst : BitVec 64) (index offset : Nat) :
    CopyBytes.copyMemory memory false src dst (BitVec.ofNat 64 index) offset=
      CopyBytes.copyMemory memory false src dst (BitVec.ofNat 64 (index+offset)) 0 := by
  simp only [CopyBytes.copyMemory,BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_zero]

theorem memoryMany_append (memory : WordWrites.Memory) (src dst index : BitVec 64) (first second : List Nat) :
    CopyBytes.memoryMany memory false src dst index (first++second)=
      CopyBytes.memoryMany (CopyBytes.memoryMany memory false src dst index first) false src dst index second := by
  induction first generalizing memory with
  | nil=>rfl
  | cons offset rest ih=>simp only [List.cons_append,CopyBytes.memoryMany]; exact ih _

/-- Consecutive original byte stores extend the copied prefix one byte at
a time, without requiring aligned source or destination pointers. -/
theorem Prefix.many (snapshot memory : WordWrites.Memory) (src dst : BitVec 64) (length index count : Nat)
    (range : Range src dst length) (prefixModel : Prefix snapshot memory src dst length index) (room : index+count≤length) :
    Prefix snapshot (CopyBytes.memoryMany memory false src dst (BitVec.ofNat 64 index) (List.range count)) src dst length (index+count) := by
  have auxiliary : ∀ count,index+count≤length → Prefix snapshot
      (CopyBytes.memoryMany memory false src dst (BitVec.ofNat 64 index) (List.range count)) src dst length (index+count) := by
    intro count
    induction count with
    | zero=>intro _room; simpa only [List.range_zero,CopyBytes.memoryMany,Nat.add_zero] using prefixModel
    | succ count ih=>
      intro room
      have previous:=ih (by omega)
      have next:=Prefix.byte_step snapshot (CopyBytes.memoryMany memory false src dst (BitVec.ofNat 64 index) (List.range count)) src dst length (index+count) range previous (by omega)
      rw [List.range_succ,memoryMany_append]
      simp only [CopyBytes.memoryMany]
      rw [copyMemory_shift]
      simpa only [Nat.add_assoc] using next
  exact auxiliary count room

/-- Both actual byte loops (eight-byte batches and single-byte tails)
reproduce every prefix byte and retain the disjoint source snapshot. -/
theorem Prefix.walk (snapshot memory : WordWrites.Memory) (src dst : BitVec 64) (length index step rounds : Nat)
    (range : Range src dst length) (prefixModel : Prefix snapshot memory src dst length index) (room : index+step*rounds≤length) :
    Prefix snapshot (CopyBytes.memoryWalk memory false src dst index step (List.range step) rounds) src dst length (index+step*rounds) := by
  induction rounds generalizing memory index with
  | zero=>simpa only [CopyBytes.memoryWalk,Nat.mul_zero,Nat.add_zero] using prefixModel
  | succ rounds ih=>
    have first:=Prefix.many snapshot memory src dst length index step range prefixModel (by rw [Nat.mul_succ] at room; omega)
    rw [CopyBytes.memoryWalk]
    have next:=ih (CopyBytes.memoryMany memory false src dst (BitVec.ofNat 64 index) (List.range step)) (index+step) first (by rw [Nat.mul_succ] at room; omega)
    simpa only [Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using next

/-- The exact unchanged memcpy byte suffix, at an arbitrary genuine
prefix index, produces all remaining snapshot bytes. -/
theorem Prefix.suffix (snapshot memory : WordWrites.Memory) (src dst : BitVec 64) (length index : Nat)
    (range : Range src dst length) (prefixModel : Prefix snapshot memory src dst length index) (ordered : index≤length) :
    Prefix snapshot (CopyGeneral.suffixMemory memory false src dst index length) src dst length length := by
  have total : index+8*((length-index)/8)+(length-index)%8=length:=by omega
  have first:=Prefix.walk snapshot memory src dst length index 8 ((length-index)/8) range prefixModel (by omega)
  have last:=Prefix.walk snapshot (CopyBytes.memoryWalk memory false src dst index 8 (List.range 8) ((length-index)/8)) src dst length
    (index+8*((length-index)/8)) 1 ((length-index)%8) range first (by omega)
  simpa only [CopyGeneral.suffixMemory,show List.range 8=CopyBytes.byteOffsets from rfl,show List.range 1=[0] from rfl,Nat.one_mul,total] using last

end InitECandidate.Solver.WitnessRadix.CopyByteContent

#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.copyMemory_shift
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.memoryMany_append
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.Prefix.many
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.Prefix.walk
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.Prefix.suffix
