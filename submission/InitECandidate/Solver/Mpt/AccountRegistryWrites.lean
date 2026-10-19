import InitECandidate.Solver.Mpt.AccountObjectGeometry
import InitECandidate.Solver.MutableTable.FamilyMemoryFrame
import InitECandidate.Solver.MutableTable.FamilyValues

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout

/-- Writes inside one registered account preserve every live pool and its
occupied values. The two reference cells are checked in the concrete write
result, so replacing a hash/root still requires a real bounded byte arena. -/
theorem Registry.after_object_writes {ι : Type}
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (account : BitVec 64) (member : account∈accounts) (writes : List (BitVec 64×BitVec 64))
    (contained : ∀ entry∈writes,∃ offset : Nat,offset<56 ∧ entry.1=account+BitVec.ofNat 64 offset)
    (root hash : BitVec 64) (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32)
    (rootCell : WordWrites.write source.memory writes (account+40#64)=.word root)
    (hashCell : WordWrites.write source.memory writes (account+48#64)=.word hash) :
    let target := {source with memory:=WordWrites.write source.memory writes}
    TableFamily.Model target cursor objects ∧ Registry target cutoff cursor objects accounts ∧
      TableFamily.ValuesHave target objects property := by
  let target := {source with memory:=WordWrites.write source.memory writes}
  obtain ⟨image⟩ := registry.images account member
  have pools : ∀ index,MemoryModel.PoolFrame source.memory target.memory (objects index).kind (objects index).plan := by
    intro index pool offset inside
    apply WordWrites.write_away
    intro found
    obtain ⟨entry,inWrites,equal⟩ := List.mem_map.mp found
    obtain ⟨position,bounded,address⟩ := contained entry inWrites
    have outside := registry.objectOutside account member position bounded index
    exact outside pool offset inside (address.symm.trans equal)
  have nextFamily := family.of_pools (target:=target) rfl rfl rfl pools
  have nextRegistry : Registry target cutoff cursor objects accounts := by
    refine ⟨registry.distinct,?_,registry.above,registry.before,registry.separated,registry.objectOutside⟩
    intro other otherMember
    by_cases same : other=account
    · subst other
      exact ⟨⟨image.output,image.domain,root,hash,rootCell,hashCell,rootArena,hashArena⟩⟩
    · obtain ⟨otherImage⟩ := registry.images other otherMember
      have preserved (offset : Nat) (inside : offset<56) : target.memory (other+BitVec.ofNat 64 offset)=source.memory (other+BitVec.ofNat 64 offset) := by
        apply WordWrites.write_away
        intro found
        obtain ⟨entry,inWrites,equal⟩ := List.mem_map.mp found
        obtain ⟨position,bounded,address⟩ := contained entry inWrites
        have numbers := congrArg BitVec.toNat (address.symm.trans equal)
        rw [image.output.slot_number account position bounded,otherImage.output.slot_number other offset inside] at numbers
        have apart := registry.separated other otherMember account member same
        rcases apart with before | after <;> omega
      exact ⟨Image.of_agreement source target other otherImage rfl (preserved 40 (by decide)) (preserved 48 (by decide))⟩
  have nextValues : TableFamily.ValuesHave target objects property := by
    apply values.of_agreement source target objects property
    intro index slot inside occupied
    have table := family.tables index
    have capNumber : (BitVec.ofNat 64 (objects index).plan.capacity).toNat=(objects index).plan.capacity := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (capacity_small (objects index).kind _ table.valid)]
    rw [capNumber] at inside
    rw [scaled_cell]
    exact pools index .values _ (word_offset_inside (objects index).kind _ .values slot.toNat (Or.inl rfl) inside)
  exact ⟨nextFamily,nextRegistry,nextValues⟩

/-- Arbitrary actual nonce/balance word writes need no additional reference
premises: both physical reference words remain exactly their current values. -/
theorem Registry.after_scalar_writes {ι : Type}
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (account : BitVec 64) (member : account∈accounts) (writes : List (BitVec 64×BitVec 64))
    (contained : ∀ entry∈writes,∃ offset : Nat,offset<40 ∧ entry.1=account+BitVec.ofNat 64 offset) :
    let target := {source with memory:=WordWrites.write source.memory writes}
    TableFamily.Model target cursor objects ∧ Registry target cutoff cursor objects accounts ∧
      TableFamily.ValuesHave target objects property := by
  obtain ⟨image⟩ := registry.images account member
  have unchanged (offset : Nat) (selected : offset=40 ∨ offset=48) :
      WordWrites.write source.memory writes (account+BitVec.ofNat 64 offset)=source.memory (account+BitVec.ofNat 64 offset) := by
    apply WordWrites.write_away
    intro found
    obtain ⟨entry,inWrites,equal⟩ := List.mem_map.mp found
    obtain ⟨position,bounded,address⟩ := contained entry inWrites
    have numbers := congrArg BitVec.toNat (address.symm.trans equal)
    rw [image.output.slot_number account position (by omega),image.output.slot_number account offset (by omega)] at numbers
    omega
  exact registry.after_object_writes source cutoff cursor objects accounts family property values account member writes
    (by intro entry found; obtain ⟨offset,small,equal⟩ := contained entry found; exact ⟨offset,by omega,equal⟩)
    image.root image.hash image.rootArena image.hashArena
    ((unchanged 40 (Or.inl rfl)).trans image.rootStored) ((unchanged 48 (Or.inr rfl)).trans image.hashStored)

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.after_object_writes
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.after_scalar_writes
