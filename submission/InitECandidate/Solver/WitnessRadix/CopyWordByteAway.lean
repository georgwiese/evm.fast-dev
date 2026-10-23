import InitECandidate.Solver.WitnessRadix.CopyWordContent
import InitECandidate.Solver.WitnessRadix.CopyByteAway

namespace InitECandidate.Solver.WitnessRadix.CopyByteContent
open Flapjack MutableTable MutableTable.CopyContents

/-- Outside an aligned whole-word byte interval, a query's physical
backing word cannot be one of the interval's write addresses. -/
theorem backing_word_away (dst query : BitVec 64) (length : Nat) (fits : dst.toNat+length<2^64)
    (aligned : dst.toNat%8=0) (multiple : length%8=0)
    (away : ∀ offset<length,query≠byteAddress dst offset) (offset : Nat) (inside : offset<length) :
    panByteAlignHOL (width:=64) query≠byteAddress dst offset := by
  intro equal
  have number:=congrArg BitVec.toNat equal
  rw [AllocatedBytes.aligned_number,byteAddress_toNat dst offset (by omega)] at number
  have offsetAligned : offset%8=0:=by omega
  have nextWord : offset+8≤length:=by omega
  have inBytes : offset+query.toNat%8<length:=by omega
  have address : query=byteAddress dst (offset+query.toNat%8):=by
    apply BitVec.eq_of_toNat_eq
    rw [byteAddress_toNat dst (offset+query.toNat%8) (by omega)]
    omega
  exact away _ inBytes address

theorem prefix_byte_away (memory : WordWrites.Memory) (src dst query : BitVec 64) (length : Nat)
    (fits : dst.toNat+length<2^64) (aligned : dst.toNat%8=0)
    (away : ∀ offset<length,query≠byteAddress dst offset) :
    byte (CopyGeneral.prefixMemory memory src dst length) query=byte memory query := by
  have before:=(CopyWords.prefix_bounds length).1
  have multiple : CopyWords.prefixIndex length%8=0:=by unfold CopyWords.prefixIndex; omega
  have absent : ∀ offset<CopyWords.prefixIndex length,panByteAlignHOL (width:=64) query≠byteAddress dst offset:=
    backing_word_away dst query (CopyWords.prefixIndex length) (by omega) aligned multiple (by intro offset inside; exact away offset (by omega))
  unfold byte
  rw [prefix_memory_truncate,prefix_words_away memory src dst (panByteAlignHOL (width:=64) query) (CopyWords.prefixIndex length) absent]

/-- Exact little-endian memcpy preserves every byte outside its genuine
byte interval, including neighbours of an unaligned final byte. -/
theorem result_byte_away (memory : WordWrites.Memory) (src dst query : BitVec 64) (length : Nat)
    (fits : dst.toNat+length<2^64) (away : ∀ offset<length,query≠byteAddress dst offset) :
    byte (CopyGeneral.resultMemory memory false src dst length) query=byte memory query := by
  unfold CopyGeneral.resultMemory
  by_cases mask : CopyGeneral.aligned src dst
  · rw [if_pos mask]
    have parts:=mask
    rw [CopyGeneral.aligned,BitVec.and_or_distrib_right,BitVec.or_eq_zero_iff] at parts
    have destinationAligned : dst.toNat%8=0:=by
      have number:=congrArg BitVec.toNat parts.1
      rw [WordBits.mask7] at number
      exact number
    have before:=(CopyWords.prefix_bounds length).1
    exact (suffix_byte_away (CopyGeneral.prefixMemory memory src dst length) src dst query (CopyWords.prefixIndex length) length before
      (by intro offset low inside; exact away offset inside)).trans (prefix_byte_away memory src dst query length fits destinationAligned away)
  · rw [if_neg mask]
    exact suffix_byte_away memory src dst query 0 length (Nat.zero_le _) (by intro offset low inside; exact away offset inside)

end InitECandidate.Solver.WitnessRadix.CopyByteContent

#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.backing_word_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.prefix_byte_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.result_byte_away
