import InitECandidate.Solver.Input.WordCodec
import Mathlib.Tactic.IntervalCases

namespace InitECandidate.Solver.Input.WordCodec
open Flapjack

set_option maxHeartbeats 1000000

theorem tuple_byte (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (index : Nat) (inside : index<8) :
    UInt8.ofNat ((Guest.wordOfLeBytes [b0,b1,b2,b3,b4,b5,b6,b7]).toNat/256^index)=
      ([b0,b1,b2,b3,b4,b5,b6,b7][index]?).getD 0 := by
  have h0 : b0.toNat<256 := b0.toNat_lt_size
  have h1 : b1.toNat<256 := b1.toNat_lt_size
  have h2 : b2.toNat<256 := b2.toNat_lt_size
  have h3 : b3.toNat<256 := b3.toNat_lt_size
  have h4 : b4.toNat<256 := b4.toNat_lt_size
  have h5 : b5.toNat<256 := b5.toNat_lt_size
  have h6 : b6.toNat<256 := b6.toNat_lt_size
  have h7 : b7.toNat<256 := b7.toNat_lt_size
  interval_cases index <;> apply UInt8.toNat.inj <;>
    simp [Guest.wordOfLeBytes,UInt8.toNat_ofNat'] <;> omega

/-- The exact byte selected from a packed little-endian host word. -/
theorem decoded_byte (bytes : List UInt8) (length : bytes.length=8) (index : Nat) (inside : index<8) :
    UInt8.ofNat ((Guest.wordOfLeBytes bytes).toNat/256^index)=(bytes[index]?).getD 0 := by
  obtain ⟨b0,t0,rfl,h0⟩:=List.length_eq_succ_iff.mp length
  obtain ⟨b1,t1,rfl,h1⟩:=List.length_eq_succ_iff.mp h0
  obtain ⟨b2,t2,rfl,h2⟩:=List.length_eq_succ_iff.mp h1
  obtain ⟨b3,t3,rfl,h3⟩:=List.length_eq_succ_iff.mp h2
  obtain ⟨b4,t4,rfl,h4⟩:=List.length_eq_succ_iff.mp h3
  obtain ⟨b5,t5,rfl,h5⟩:=List.length_eq_succ_iff.mp h4
  obtain ⟨b6,t6,rfl,h6⟩:=List.length_eq_succ_iff.mp h5
  obtain ⟨b7,t7,rfl,h7⟩:=List.length_eq_succ_iff.mp h6
  have empty : t7=[]:=List.length_eq_zero_iff.mp h7
  subst t7
  exact tuple_byte _ _ _ _ _ _ _ _ index inside

end InitECandidate.Solver.Input.WordCodec

#print axioms InitECandidate.Solver.Input.WordCodec.tuple_byte
#print axioms InitECandidate.Solver.Input.WordCodec.decoded_byte
