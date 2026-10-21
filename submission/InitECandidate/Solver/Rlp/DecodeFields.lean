import InitECandidate.Solver.Rlp.DecodeNormal
import InitECandidate.Solver.Rlp.ItemCallEncoding

namespace InitECandidate.Solver.Rlp.Decode
open Flapjack

/-- The actual full item tuple uniquely identifies its header/payload/kind,
so its complete-extent facts apply to those same returned words. -/
theorem Complete.fields (pointer length header payload flag : BitVec 64)
    (complete : Complete pointer length (Item.result pointer header payload flag)) :
    header.toNat≤9 ∧ 1≤header.toNat+payload.toNat ∧ header.toNat+payload.toNat=length.toNat ∧
      (flag=0#64 ∨ flag=1#64) ∧ (flag=1#64 → 1≤header.toNat) := by
  obtain ⟨oldHeader,oldPayload,oldFlag,same,small,positive,extent,binary,listHeader⟩ := complete
  obtain ⟨rfl,rfl,rfl⟩ := Item.result_injective pointer header payload flag oldHeader oldPayload oldFlag same
  exact ⟨small,positive,extent,binary,listHeader⟩

end InitECandidate.Solver.Rlp.Decode

#print axioms InitECandidate.Solver.Rlp.Decode.Complete.fields
