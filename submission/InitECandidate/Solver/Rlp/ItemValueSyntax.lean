import InitECandidate.Solver.Rlp.ItemSyntax
import InitECandidate.Solver.Rlp.HeaderValue

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

/-- The actual returned quad determines its header, payload and flag. -/
theorem result_injective (pointer h p f h' p' f' : BitVec 64)
    (same : result pointer h p f=result pointer h' p' f') : h=h' ∧ p=p' ∧ f=f' := by
  simp only [result,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,BitVec.add_right_inj] at same
  exact ⟨same.2.1,same.2.2.1,same.1⟩

theorem Valid.result_fields (pointer header payload flag : BitVec 64) (length : Nat)
    (valid : Valid pointer length (result pointer header payload flag)) :
    header.toNat≤9 ∧ 1≤header.toNat+payload.toNat ∧ header.toNat+payload.toNat≤length ∧
      (flag=0#64 ∨ flag=1#64) ∧ (flag=1#64→1≤header.toNat) := by
  obtain ⟨actualHeader,actualPayload,actualFlag,same,small,positive,bounded,binary,listHeader⟩:=valid
  obtain ⟨rfl,rfl,rfl⟩:=result_injective pointer header payload flag actualHeader actualPayload actualFlag same
  exact ⟨small,positive,bounded,binary,listHeader⟩

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

#print axioms InitECandidate.Solver.Rlp.Item.result_injective
#print axioms InitECandidate.Solver.Rlp.Item.Valid.result_fields
