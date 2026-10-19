import InitECandidate.Solver.Rlp.ReadLengthUnique

namespace InitECandidate.Solver.Rlp.ReadLength
open Flapjack PanSemStateFiniteExact

theorem BytesAgree.subspan (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length offset : BitVec 64) (bytes : Nat) (agreement : BytesAgree source target pointer length)
    (inside : offset.toNat+bytes≤length.toNat) :
    ∀ index : BitVec 64,index.toNat<bytes → byte source (pointer+offset+index)=byte target (pointer+offset+index) := by
  intro index bounded
  have number : (offset+index).toNat=offset.toNat+index.toNat := BitVec.toNat_add_of_lt (by have := length.isLt; omega)
  have actual := agreement (offset+index) (by rw [number]; omega)
  simpa only [BitVec.add_assoc] using actual

end InitECandidate.Solver.Rlp.ReadLength

#print axioms InitECandidate.Solver.Rlp.ReadLength.BytesAgree.subspan
