import InitECandidate.Solver.Mpt.AccountRegistryWrites
import InitECandidate.Solver.Input.RlpWrite.U256Store

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix QueryBranch MutableTable

/-- An actual scalar store in the nonce/balance part of a registered record
executes from its mapped current object and retains all runtime ownership. -/
theorem Registry.scalar_store {ι : Type}
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (account : BitVec 64) (member : account∈accounts) (offset : Nat) (inside : offset<40) (aligned : offset%8=0)
    (destination expression : ExpHOL 64) (value : BitVec 64)
    (destinationRead : eval source destination=some (.val (.word (account+BitVec.ofNat 64 offset))))
    (valueRead : eval source expression=some (.val (.word value))) :
    let target := {source with memory:=StoreWord.put source.memory (account+BitVec.ofNat 64 offset) value}
    evaluateHOLFiniteState source (.store destination expression)=(none,target) ∧
      TableFamily.Model target cursor objects ∧ Registry target cutoff cursor objects accounts ∧ TableFamily.ValuesHave target objects property := by
  obtain ⟨image⟩ := registry.images account member
  have mapped : source.memaddrs (account+BitVec.ofNat 64 offset) := by
    rw [image.domain]
    exact image.output.word_mapped account offset (by omega) aligned
  have retained := registry.after_scalar_writes source cutoff cursor objects accounts family property values account member
    [(account+BitVec.ofNat 64 offset,value)] (by
      intro entry found
      have same : entry=(account+BitVec.ofNat 64 offset,value) := by simpa using found
      subst entry
      exact ⟨offset,inside,rfl⟩)
  exact ⟨StoreWord.execute source destination expression _ value destinationRead valueRead mapped,retained⟩

/-- The original four-limb balance store has a derived exact memory effect,
zero source ticks and retained tables, cache ownership and account images. -/
theorem Registry.balance_store {ι : Type}
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (account : BitVec 64) (member : account∈accounts) (destination expression : ExpHOL 64) (words : Input.RlpWrite.U256Value.Words)
    (destinationRead : eval source destination=some (.val (.word (account+8#64))))
    (valueRead : eval source expression=some (Input.RlpWrite.U256Value.tuple words)) :
    let target := {source with memory:=WordWrites.write source.memory (Input.RlpWrite.U256Value.wordWrites (account+8#64) words)}
    evaluateHOLFiniteState source (.store destination expression)=(none,target) ∧
      TableFamily.Model target cursor objects ∧ Registry target cutoff cursor objects accounts ∧ TableFamily.ValuesHave target objects property := by
  obtain ⟨image⟩ := registry.images account member
  have mapped (index : Fin 4) : source.memaddrs (account+8#64+BitVec.ofNat 64 (8*index.val)) := by
    rw [image.domain]
    have bound := index.isLt
    have mappedField := image.output.word_mapped account (8+8*index.val) (by omega) (by omega)
    simpa [BitVec.ofNat_add,BitVec.add_assoc] using mappedField
  have retained := registry.after_scalar_writes source cutoff cursor objects accounts family property values account member
    (Input.RlpWrite.U256Value.wordWrites (account+8#64) words) (by
      intro entry found
      simp only [Input.RlpWrite.U256Value.wordWrites,List.mem_cons,List.not_mem_nil,or_false] at found
      rcases found with rfl | rfl | rfl | rfl
      · exact ⟨8,by decide,rfl⟩
      · exact ⟨16,by decide,by simp [BitVec.add_assoc]⟩
      · exact ⟨24,by decide,by simp [BitVec.add_assoc]⟩
      · exact ⟨32,by decide,by simp [BitVec.add_assoc]⟩)
  exact ⟨Input.RlpWrite.U256Value.store_execute source destination expression _ words destinationRead valueRead mapped,retained⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.scalar_store
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.balance_store
