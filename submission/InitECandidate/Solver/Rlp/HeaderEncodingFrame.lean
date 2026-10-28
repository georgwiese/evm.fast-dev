import InitECandidate.Solver.Rlp.HeaderEncoding

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem observed_shift_transport (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer ll header payload : BitVec 64) (small : ll.toNat≤8) (head : header=1#64+ll)
    (observed : ReadLength.Observed source (pointer+1#64) ll payload)
    (bytes : ∀ offset : BitVec 64,offset.toNat<max 1 header.toNat →
      ReadLength.byte source (pointer+offset)=ReadLength.byte target (pointer+offset)) :
    ReadLength.Observed target (pointer+1#64) ll payload := by
  have headerNumber : header.toNat=1+ll.toNat := by
    rw [head,BitVec.toNat_add_of_lt (by change 1+ll.toNat<2^64; omega)]
    rfl
  apply ReadLength.Observed.transport source target _ _ _ observed
  intro offset inside
  have number : (1#64+offset).toNat=1+offset.toNat := by
    rw [BitVec.toNat_add_of_lt (by change 1+offset.toNat<2^64; omega)]
    rfl
  have selected := bytes (1#64+offset) (by rw [number,headerNumber]; omega)
  simpa only [BitVec.add_assoc] using selected

/-- An encoding depends only on its real header bytes, with the single
byte form occupying one byte even though its header word is zero. -/
theorem Encoded.transport (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag : BitVec 64) (encoded : Encoded source pointer header payload flag)
    (bytes : ∀ offset : BitVec 64,offset.toNat<max 1 header.toNat →
      ReadLength.byte source (pointer+offset)=ReadLength.byte target (pointer+offset)) :
    Encoded target pointer header payload flag := by
  obtain ⟨loaded,first,encoding⟩ := encoded
  have firstEq : ReadLength.byte source pointer=ReadLength.byte target pointer := by
    simpa only [BitVec.add_zero] using bytes 0#64 (by change 0<max 1 header.toNat; omega)
  have firstAfter : ReadLength.byte target pointer=some loaded := firstEq.symm.trans first
  refine ⟨loaded,firstAfter,?_⟩
  dsimp only at encoding ⊢
  let b := BitVec.ofNat 64 loaded.toNat
  have bSmall : b.toNat<256 := by
    have bounded : loaded.toNat<256 := loaded.toNat_lt_size
    change (BitVec.ofNat 64 loaded.toNat).toNat<256
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    exact bounded
  split_ifs at encoding ⊢ with singleCase shortStringCase longStringCase shortListCase
  · exact encoding
  · exact encoding
  · have lower : 183≤b.toNat := by change ¬b.toNat≤183 at shortStringCase; omega
    have difference : (b-183#64).toNat=b.toNat-183 := by
      rw [BitVec.toNat_sub_of_le (by change 183≤b.toNat; exact lower)]
      rfl
    have small : (b-183#64).toNat≤8 := by rw [difference]; change b.toNat≤191 at longStringCase; omega
    exact ⟨encoding.1,encoding.2.1,observed_shift_transport source target pointer (b-183#64) header payload
      small encoding.1 encoding.2.2 bytes⟩
  · exact encoding
  · have lower : 247≤b.toNat := by change ¬b.toNat≤247 at shortListCase; omega
    have difference : (b-247#64).toNat=b.toNat-247 := by
      rw [BitVec.toNat_sub_of_le (by change 247≤b.toNat; exact lower)]
      rfl
    have small : (b-247#64).toNat≤8 := by rw [difference]; omega
    exact ⟨encoding.1,encoding.2.1,observed_shift_transport source target pointer (b-247#64) header payload
      small encoding.1 encoding.2.2 bytes⟩

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.observed_shift_transport
#print axioms InitECandidate.Solver.Rlp.Header.Encoded.transport
