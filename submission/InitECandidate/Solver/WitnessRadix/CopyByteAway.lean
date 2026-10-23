import InitECandidate.Solver.WitnessRadix.CopyBytePrefix

namespace InitECandidate.Solver.WitnessRadix.CopyByteContent
open Flapjack MutableTable.CopyContents

/-- Byte-copy batches preserve every other byte, including neighbouring
lanes sharing a physical destination word. -/
theorem many_byte_away (memory : WordWrites.Memory) (src dst index query : BitVec 64) (offsets : List Nat)
    (away : ∀ offset∈offsets,query≠dst+index+BitVec.ofNat 64 offset) :
    byte (CopyBytes.memoryMany memory false src dst index offsets) query=byte memory query := by
  induction offsets generalizing memory with
  | nil=>rfl
  | cons offset rest ih=>
    rw [CopyBytes.memoryMany,ih _ (by intro index member; exact away index (List.mem_cons_of_mem _ member)),byte_copy_projection]
    rw [if_neg (away offset (by simp))]

/-- Both original byte loops preserve byte values outside their genuine
write indices; no source/destination alignment premise is needed. -/
theorem walk_byte_away (memory : WordWrites.Memory) (src dst query : BitVec 64) (index step rounds : Nat) (offsets : List Nat)
    (offsetBound : ∀ offset∈offsets,offset<step)
    (away : ∀ offset,index≤offset → offset<index+step*rounds → query≠byteAddress dst offset) :
    byte (CopyBytes.memoryWalk memory false src dst index step offsets rounds) query=byte memory query := by
  induction rounds generalizing memory index with
  | zero=>rfl
  | succ rounds ih=>
    rw [CopyBytes.memoryWalk,ih _ (index+step) (by intro offset low high; exact away offset (by omega) (by rw [Nat.mul_succ]; omega))]
    apply many_byte_away
    intro offset member
    have bound:=offsetBound offset member
    have different:=away (index+offset) (by omega) (by rw [Nat.mul_succ]; omega)
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using different

theorem suffix_byte_away (memory : WordWrites.Memory) (src dst query : BitVec 64) (index length : Nat)
    (ordered : index≤length)
    (away : ∀ offset,index≤offset → offset<length → query≠byteAddress dst offset) :
    byte (CopyGeneral.suffixMemory memory false src dst index length) query=byte memory query := by
  have total : index+8*((length-index)/8)+(length-index)%8=length:=by omega
  unfold CopyGeneral.suffixMemory
  rw [walk_byte_away _ src dst query (index+8*((length-index)/8)) 1 ((length-index)%8) [0]
    (by intro offset member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst offset; decide)
    (by intro offset low high; exact away offset (by omega) (by omega))]
  exact walk_byte_away memory src dst query index 8 ((length-index)/8) CopyBytes.byteOffsets
    (by intro offset member; simp only [CopyBytes.byteOffsets,List.mem_cons,List.not_mem_nil,or_false] at member; omega)
    (by intro offset low high; exact away offset low (by omega))

end InitECandidate.Solver.WitnessRadix.CopyByteContent

#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.many_byte_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.walk_byte_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.suffix_byte_away
