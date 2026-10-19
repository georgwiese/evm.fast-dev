import InitECandidate.Solver.Rlp.ItemEntry

namespace InitECandidate.Solver.Rlp.Item
open Flapjack WitnessRadix WitnessRadix.QueryBranch

def result (pointer header payload flag : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word flag),.val (.word (pointer+header)),.val (.word payload),.val (.word (header+payload))]

/-- Current original item result, including its real payload pointer and
positive nonwrapping total inside the actual passed input extent. -/
def Valid (pointer : BitVec 64) (length : Nat) (value : ValueHOL 64) : Prop :=
  ∃ header payload flag,value=result pointer header payload flag ∧ header.toNat≤9 ∧
    1≤header.toNat+payload.toNat ∧ header.toNat+payload.toNat≤length ∧
    (flag=0#64 ∨ flag=1#64) ∧ (flag=1#64 → 1≤header.toNat)

theorem Valid.payload_span (domain : BitVec 64 → Prop) (pointer : BitVec 64) (length : Nat) (value : ValueHOL 64)
    (valid : Valid pointer length value) (fits : pointer.toNat+length<2^64)
    (mapped : ∀ offset<length,domain (panByteAlignHOL (width:=64) (byteAddress pointer offset))) :
    ∃ header payload flag,value=result pointer header payload flag ∧
      (pointer+header).toNat+payload.toNat<2^64 ∧ payload.toNat≤length ∧
      ∀ offset<payload.toNat,domain (panByteAlignHOL (width:=64) (byteAddress (pointer+header) offset)) := by
  obtain ⟨header,payload,flag,same,small,positive,bounded,binary,listHeader⟩ := valid
  obtain ⟨nonwrapping,payloadMapped⟩ := Header.payload_span domain pointer header payload length fits mapped bounded
  exact ⟨header,payload,flag,same,nonwrapping,by omega,payloadMapped⟩

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.Valid.payload_span
