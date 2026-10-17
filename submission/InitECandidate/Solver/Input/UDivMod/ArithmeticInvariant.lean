import InitECandidate.Solver.Input.UDivMod.ArithmeticBits

namespace InitECandidate.Solver.Input.UDivMod

/-- Natural conservation through the actual bit-by-bit unsigned division.
The unprocessed low input bits remain explicit, so modular multiplication
cannot masquerade as a correct quotient. -/
structure Arithmetic (a b q r : BitVec 64) (index : Nat) : Prop where
  remainder : r.toNat<b.toNat
  aligned : q.toNat%2^index=0
  conserved : b.toNat*q.toNat+r.toNat*2^index+a.toNat%2^index=a.toNat

theorem arithmetic_initial (a b : BitVec 64) (positive : 0<b.toNat) : Arithmetic a b 0#64 0#64 64 := by
  refine ⟨positive,by simp,?_⟩
  change b.toNat*0+0*2^64+a.toNat%2^64=a.toNat
  simp [Nat.mod_eq_of_lt a.isLt]

theorem arithmetic_step (a b q r : BitVec 64) (index : Nat) (small : index<64) (bSmall : b.toNat≤2^63)
    (invariant : Arithmetic a b q r (index+1)) :
    Arithmetic a b (nextQ a b q r (index+1)) (nextR a b r (index+1)) index := by
  have bitSmall:=inputBit_lt a index
  have shiftedNat : (shifted a r (index+1)).toNat=2*r.toNat+inputBit a index := by
    simpa only [Nat.add_sub_cancel] using shifted_number a r (index+1) (by have h:=invariant.remainder; omega)
  have alignedDown : q.toNat%2^index=0 := by
    have down:=Nat.mod_mul_right_mod q.toNat (2^index) 2
    rw [←Nat.pow_succ,invariant.aligned] at down
    simpa using down.symm
  have old:=invariant.conserved
  rw [input_remainder_split,Nat.pow_succ] at old
  by_cases take : takeSubtract a b r (index+1)
  · have qNat : (nextQ a b q r (index+1)).toNat=q.toNat+2^index := by
      simp only [nextQ,if_pos take,Nat.add_sub_cancel]
      exact set_bit_number q index small invariant.aligned
    have rNat : (nextR a b r (index+1)).toNat=(shifted a r (index+1)).toNat-b.toNat := by
      simp only [nextR,if_pos take]
      exact BitVec.toNat_sub_of_le (show b≤shifted a r (index+1) from take)
    have subtract : (nextR a b r (index+1)).toNat+b.toNat=2*r.toNat+inputBit a index := by
      rw [rNat]
      change b.toNat≤(shifted a r (index+1)).toNat at take
      omega
    refine ⟨?_,?_,?_⟩
    · have oldR:=invariant.remainder
      omega
    · rw [qNat]
      simp [Nat.add_mod,alignedDown]
    · rw [qNat]
      have weighted:=congrArg (fun value : Nat=>value*2^index) subtract
      nlinarith [weighted]
  · have qNat : (nextQ a b q r (index+1)).toNat=q.toNat := by simp only [nextQ,if_neg take]
    have rNat : (nextR a b r (index+1)).toNat=2*r.toNat+inputBit a index := by simp only [nextR,if_neg take]; exact shiftedNat
    refine ⟨?_,?_,?_⟩
    · change ¬b.toNat≤(shifted a r (index+1)).toNat at take
      rw [rNat]
      omega
    · rw [qNat]
      exact alignedDown
    · rw [qNat,rNat]
      nlinarith [old]

theorem arithmetic_finish (a b q r : BitVec 64) (invariant : Arithmetic a b q r 0) :
    q.toNat=a.toNat/b.toNat ∧ r.toNat=a.toNat%b.toNat := by
  have positive : 0<b.toNat := by have h:=invariant.remainder; omega
  have conserved : b.toNat*q.toNat+r.toNat=a.toNat := by simpa only [Nat.pow_zero,Nat.mul_one,Nat.mod_one,Nat.add_zero] using invariant.conserved
  constructor
  · rw [←conserved,Nat.mul_add_div positive,Nat.div_eq_of_lt invariant.remainder,Nat.add_zero]
  · rw [←conserved,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt invariant.remainder]

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.arithmetic_initial
#print axioms InitECandidate.Solver.Input.UDivMod.arithmetic_step
#print axioms InitECandidate.Solver.Input.UDivMod.arithmetic_finish
