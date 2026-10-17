import InitECandidate.Solver.Input.WordCodec

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Input.WordCodec

theorem or_upper (low high shift : Nat) (small : low<2^shift) :
    low ||| (high*2^shift)=low+high*2^shift := by
  rw [Nat.or_comm,Nat.mul_comm,←Nat.two_pow_add_eq_or_of_lt small high]
  omega

def word4 (b0 b1 b2 b3 : BitVec 64) : BitVec 64 :=
  b0 ||| ((b1 <<< (8:Nat)) ||| ((b2 <<< (16:Nat)) ||| (b3 <<< (24:Nat))))

theorem word4_eq (b0 b1 b2 b3 : Nat) (h0 : b0<256) (h1 : b1<256) (h2 : b2<256) (h3 : b3<256) :
    word4 (BitVec.ofNat 64 b0) (BitVec.ofNat 64 b1) (BitVec.ofNat 64 b2) (BitVec.ofNat 64 b3)=
      BitVec.ofNat 64 (b0+b1*256+b2*65536+b3*16777216) := by
  have w0 : b0<2^64 := by omega
  have w1 : b1<2^64 := by omega
  have w2 : b2<2^64 := by omega
  have w3 : b3<2^64 := by omega
  have s1 : b1*2^8<2^64 := by
    calc b1*2^8<256*2^8 := Nat.mul_lt_mul_of_pos_right h1 (by decide)
         _<2^64 := by decide
  have s2 : b2*2^16<2^64 := by
    calc b2*2^16<256*2^16 := Nat.mul_lt_mul_of_pos_right h2 (by decide)
         _<2^64 := by decide
  have s3 : b3*2^24<2^64 := by
    calc b3*2^24<256*2^24 := Nat.mul_lt_mul_of_pos_right h3 (by decide)
         _<2^64 := by decide
  have sum : b0+b1*256+b2*65536+b3*16777216<2^64 := by
    clear w0 w1 w2 w3 s1 s2 s3
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [word4,BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt w0,Nat.mod_eq_of_lt w1,Nat.mod_eq_of_lt w2,Nat.mod_eq_of_lt w3,
    Nat.mod_eq_of_lt s1,Nat.mod_eq_of_lt s2,Nat.mod_eq_of_lt s3,Nat.mod_eq_of_lt sum]
  rw [←Nat.or_assoc,←Nat.or_assoc,or_upper b0 b1 8 h0,
    or_upper (b0+b1*2^8) b2 16 (by omega),
    or_upper (b0+b1*2^8+b2*2^16) b3 24 (by omega)]

def word8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 64) : BitVec 64 :=
  word4 b0 b1 b2 b3 ||| ((word4 b4 b5 b6 b7) <<< (32:Nat))

theorem word8_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (h0 : b0<256) (h1 : b1<256) (h2 : b2<256) (h3 : b3<256)
    (h4 : b4<256) (h5 : b5<256) (h6 : b6<256) (h7 : b7<256) :
    word8 (BitVec.ofNat 64 b0) (BitVec.ofNat 64 b1) (BitVec.ofNat 64 b2) (BitVec.ofNat 64 b3)
      (BitVec.ofNat 64 b4) (BitVec.ofNat 64 b5) (BitVec.ofNat 64 b6) (BitVec.ofNat 64 b7)=
      BitVec.ofNat 64 ((b0+b1*256+b2*65536+b3*16777216)+
        (b4+b5*256+b6*65536+b7*16777216)*4294967296) := by
  rw [word8,word4_eq _ _ _ _ h0 h1 h2 h3,word4_eq _ _ _ _ h4 h5 h6 h7]
  have low : b0+b1*256+b2*65536+b3*16777216<2^32 := by omega
  have high : b4+b5*256+b6*65536+b7*16777216<2^32 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show b0+b1*256+b2*65536+b3*16777216<2^64 by omega),
    Nat.mod_eq_of_lt (show b4+b5*256+b6*65536+b7*16777216<2^64 by omega),
    Nat.mod_eq_of_lt (show (b4+b5*256+b6*65536+b7*16777216)*2^32<2^64 by omega),
    Nat.mod_eq_of_lt (show (b0+b1*256+b2*65536+b3*16777216)+(b4+b5*256+b6*65536+b7*16777216)*4294967296<2^64 by omega)]
  exact or_upper _ _ 32 low

end InitECandidate.Solver.Input.WordCodec

#print axioms InitECandidate.Solver.Input.WordCodec.or_upper
#print axioms InitECandidate.Solver.Input.WordCodec.word4_eq
#print axioms InitECandidate.Solver.Input.WordCodec.word8_eq
