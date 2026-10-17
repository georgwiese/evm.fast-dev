import InitECandidate.Solver.Input.UDivMod.Program
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace InitECandidate.Solver.Input.UDivMod

def inputBit (a : BitVec 64) (index : Nat) : Nat := a.toNat/2^index%2

theorem inputBit_lt (a : BitVec 64) (index : Nat) : inputBit a index<2 := Nat.mod_lt _ (by decide)

theorem inputBit_number (a : BitVec 64) (index : Nat) :
    ((a>>>(index:Nat)) &&& 1#64).toNat=inputBit a index := by
  rw [BitVec.toNat_and,BitVec.toNat_ushiftRight]
  change (a.toNat>>>index) &&& 1=inputBit a index
  rw [Nat.shiftRight_eq_div_pow,Nat.and_comm,Nat.one_and_eq_mod_two]
  rfl

theorem double_number (r : BitVec 64) (small : r.toNat<2^63) :
    (r<<<(1:Nat)).toNat=2*r.toNat := by
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (r.toNat*2)%2^64=2*r.toNat
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The remainder shift/low-bit OR is exact natural arithmetic, with no
64-bit overflow whenever the old remainder is below2^63. -/
theorem shifted_number (a r : BitVec 64) (index : Nat) (small : r.toNat<2^63) :
    (shifted a r index).toNat=2*r.toNat+inputBit a (index-1) := by
  rw [shifted,BitVec.toNat_or,double_number r small,inputBit_number]
  have joined:=Nat.two_pow_add_eq_or_of_lt (i:=1) (inputBit_lt a (index-1)) r.toNat
  exact joined.symm

theorem one_shift_number (index : Nat) (small : index<64) :
    (1#64<<<index).toNat=2^index := by
  have bound : 2^index<2^64:=Nat.pow_lt_pow_right (by decide) small
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (1*2^index)%2^64=2^index
  rw [Nat.one_mul,Nat.mod_eq_of_lt bound]

/-- The quotient contains no bits below the current boundary. Setting its
next bit therefore agrees with natural addition, without a wrap assumption. -/
theorem set_bit_number (q : BitVec 64) (index : Nat) (small : index<64)
    (aligned : q.toNat%2^(index+1)=0) :
    (q ||| (1#64<<<index)).toNat=q.toNat+2^index := by
  have split:=Nat.mod_add_div q.toNat (2^(index+1))
  rw [aligned,Nat.zero_add] at split
  have bitSmall : 2^index<2^(index+1) := by
    rw [Nat.pow_succ]
    have positive:=Nat.two_pow_pos index
    omega
  have joined:=Nat.two_pow_add_eq_or_of_lt bitSmall (q.toNat/2^(index+1))
  rw [split] at joined
  rw [BitVec.toNat_or,one_shift_number index small]
  exact joined.symm

theorem input_remainder_split (a : BitVec 64) (index : Nat) :
    a.toNat%2^(index+1)=inputBit a index*2^index+a.toNat%2^index := by
  rw [Nat.pow_succ,Nat.mod_mul]
  simp only [inputBit]
  ring

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.shifted_number
#print axioms InitECandidate.Solver.Input.UDivMod.set_bit_number
#print axioms InitECandidate.Solver.Input.UDivMod.input_remainder_split
