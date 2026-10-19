import InitECandidate.Solver.Mpt.AccountRegistry
import InitECandidate.Solver.Input.StoreWordsNormal
import InitECandidate.Solver.Rlp.SliceArrayModel

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem Output.word_mapped (out : BitVec 64) (output : Output out) (offset : Nat)
    (inside : offset+8≤56) (aligned : offset%8=0) : InitE.ordinaryDomain (out+BitVec.ofNat 64 offset) := by
  apply BackingLayout.ordinary_mapped
  · rw [output.slot_number out offset (by omega)]
    have := output.lower
    omega
  · rw [output.slot_number out offset (by omega)]
    have := output.upper
    omega
  · rw [output.slot_number out offset (by omega),Nat.add_mod,output.aligned,aligned]

theorem Output.outside_slot (out query : BitVec 64) (output : Output out) (offset : Nat) (inside : offset<56)
    (outside : query.toNat<out.toNat ∨ out.toNat+56≤query.toNat) : query≠out+BitVec.ofNat 64 offset := by
  intro equal
  have number := congrArg BitVec.toNat equal
  rw [output.slot_number out offset inside] at number
  rcases outside with before | after <;> omega

/-- A real tuple store contained in the account's56-byte allocation retains
every ordinary word outside it, without assuming future store success. -/
theorem Output.stores_away (out query : BitVec 64) (output : Output out)
    (offset : Nat) (values : List (HolWordLab 64)) (extent : offset+8*values.length≤56)
    (domain : BitVec 64 → Prop) (memory result : WordWrites.Memory)
    (normal : @panMemStoresHOL 64 _ (out+BitVec.ofNat 64 offset) values domain (fun address=>Classical.propDecidable (domain address)) memory=some result)
    (outside : query.toNat<out.toNat ∨ out.toNat+56≤query.toNat) : result query=memory query := by
  apply Input.words_away values (out+BitVec.ofNat 64 offset) query domain memory result normal
  intro index active
  have inside : offset+8*index<56 := by omega
  have apart := output.outside_slot out query (offset+8*index) inside outside
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using apart

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Output.outside_slot
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Output.stores_away
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Output.word_mapped
