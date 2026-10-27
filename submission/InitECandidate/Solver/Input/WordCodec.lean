import Mathlib.Data.List.Basic
import InitE.SourceSemantics
import Flapjack.Pancake.Semantics.ShMemBytesBridge

namespace InitECandidate.Solver.Input.WordCodec
open Flapjack

theorem guest_roundtrip (word : BitVec 64) : Guest.wordOfLeBytes (Guest.leBytes word)=word := by
  have bound := word.isLt
  apply BitVec.eq_of_toNat_eq
  simp [Guest.wordOfLeBytes,Guest.leBytes,List.range_succ,UInt8.toNat_ofNat']
  omega

theorem pan_bytes (word : BitVec 64) : panWordToBytesHOL word false=(Guest.leBytes word).map byteToBits := by
  rw [panWordToBytesHOL_eq_map_crepClockWordToBytes]
  simp only [crepClockWordToBytes,Guest.leBytes,List.map_map]
  apply List.map_congr_left
  intro index member
  have power : 2^(8*index)=(256 : Nat)^index := by rw [Nat.pow_mul]
  simp [Function.comp_apply,power,byteToBits,UInt8.toBitVec_ofNat']

theorem oracle_address (word : BitVec 64) : Guest.wordOfLeBytes ((panWordToBytesHOL word false).map bitsToByte)=word := by
  rw [pan_bytes,List.map_map]
  simp only [Function.comp_def,bitsToByte_byteToBits,List.map_id']
  exact guest_roundtrip word

theorem leSumB_guest (bytes : List UInt8) (index : Nat) :
    leSumB index (bytes.map byteToBits)=(256^index)*bytes.foldr (fun byte acc => acc*256+byte.toNat) 0 := by
  induction bytes generalizing index with
  | nil => simp [leSumB]
  | cons byte rest ih =>
    rw [List.map_cons,leSumB_cons,byteToBits_toNat,ih,List.foldr_cons,Nat.pow_succ,Nat.mul_add]
    ac_rfl

theorem pan_word_guest (bytes : List UInt8) (length : bytes.length≤8) :
    panWordOfBytesHOL (width := 64) false 0 (bytes.map byteToBits)=Guest.wordOfLeBytes bytes := by
  rw [show (0 : BitVec 64)=BitVec.ofNat 64 0 from rfl,
    panWordOfBytesHOL_eq_ofNat_le 0 _ (by simp only [List.length_map,Nat.zero_add]; exact length),leSumB_guest]
  simp [Guest.wordOfLeBytes]

theorem pan_roundtrip (word : BitVec 64) : panWordOfBytesHOL (width := 64) false 0 (panWordToBytesHOL word false)=word := by
  rw [pan_bytes,pan_word_guest _ (by simp [Guest.leBytes]),guest_roundtrip]

end InitECandidate.Solver.Input.WordCodec

#print axioms InitECandidate.Solver.Input.WordCodec.guest_roundtrip
#print axioms InitECandidate.Solver.Input.WordCodec.pan_bytes
#print axioms InitECandidate.Solver.Input.WordCodec.oracle_address

#print axioms InitECandidate.Solver.Input.WordCodec.leSumB_guest
#print axioms InitECandidate.Solver.Input.WordCodec.pan_word_guest
#print axioms InitECandidate.Solver.Input.WordCodec.pan_roundtrip
