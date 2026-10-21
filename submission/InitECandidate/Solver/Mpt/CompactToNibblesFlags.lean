import InitECandidate.Solver.Mpt.CompactToNibblesInitial

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem one_bit_binary (word : BitVec 64) : word&&&1#64=0#64 ∨ word&&&1#64=1#64 := by
  have bounded : (word&&&1#64).toNat≤1:=by rw [BitVec.toNat_and]; exact Nat.and_le_right
  have cases : (word&&&1#64).toNat=0 ∨ (word&&&1#64).toNat=1:=by omega
  rcases cases with zero|one
  · exact Or.inl (BitVec.eq_of_toNat_eq zero)
  · exact Or.inr (BitVec.eq_of_toNat_eq one)

theorem prepared_flags (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte : BitVec 64) :
    (prepared source byte).locals.lookup (ofString "odd")=some (.val (.word ((byte>>>4)&&&1#64))) ∧
    (prepared source byte).locals.lookup (ofString "is_leaf")=some (.val (.word ((byte>>>4>>>1)&&&1#64))) ∧
    (((byte>>>4)&&&1#64)=0#64 ∨ ((byte>>>4)&&&1#64)=1#64) ∧
    (((byte>>>4>>>1)&&&1#64)=0#64 ∨ ((byte>>>4>>>1)&&&1#64)=1#64) := by
  refine ⟨bind_lookup_same _ _ _,?_,one_bit_binary _,one_bit_binary _⟩
  exact (bind_lookup_other _ "odd" "is_leaf" _ (by decide)).trans (bind_lookup_same _ _ _)

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.one_bit_binary
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.prepared_flags
