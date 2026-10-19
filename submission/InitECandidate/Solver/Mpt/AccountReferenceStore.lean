import InitECandidate.Solver.Mpt.AccountStoreRegistered

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix QueryBranch MutableTable

theorem Registry.reference_store {ι : Type}
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (account : BitVec 64) (member : account ∈ accounts) (offset : Nat) (selected : offset = 40 ∨ offset = 48)
    (destination expression : ExpHOL 64) (reference : BitVec 64) (arena : AllocatedBytes.Arena reference 32)
    (destinationRead : eval source destination = some (.val (.word (account + BitVec.ofNat 64 offset))))
    (valueRead : eval source expression = some (.val (.word reference))) :
    let target := {source with memory := StoreWord.put source.memory (account + BitVec.ofNat 64 offset) reference}
    evaluateHOLFiniteState source (.store destination expression) = (none,target) ∧
      TableFamily.Model target cursor objects ∧ Registry target cutoff cursor objects accounts ∧ TableFamily.ValuesHave target objects property := by
  obtain ⟨image⟩ := registry.images account member
  have different : account + 40#64 ≠ account + 48#64 := by
    intro same
    have numbers := congrArg BitVec.toNat same
    rw [image.output.slot_number account 40 (by decide),image.output.slot_number account 48 (by decide)] at numbers
    omega
  rcases selected with rfl | rfl
  · have mapped : source.memaddrs (account + 40#64) := by rw [image.domain]; exact image.output.word_mapped account 40 (by decide) (by decide)
    have retained := registry.after_object_writes source cutoff cursor objects accounts family property values account member [(account + 40#64,reference)]
      (by
        intro entry found
        have same : entry = (account + 40#64,reference) := by simpa using found
        subst entry
        exact ⟨40,by decide,rfl⟩)
      reference image.hash arena image.hashArena
      (by simp [WordWrites.write,StoreWord.put])
      (by simpa [WordWrites.write,StoreWord.put,Ne.symm different] using image.hashStored)
    exact ⟨StoreWord.execute source destination expression _ reference destinationRead valueRead mapped,retained⟩
  · have mapped : source.memaddrs (account + 48#64) := by rw [image.domain]; exact image.output.word_mapped account 48 (by decide) (by decide)
    have retained := registry.after_object_writes source cutoff cursor objects accounts family property values account member [(account + 48#64,reference)]
      (by
        intro entry found
        have same : entry = (account + 48#64,reference) := by simpa using found
        subst entry
        exact ⟨48,by decide,rfl⟩)
      image.root reference image.rootArena arena
      (by simpa [WordWrites.write,StoreWord.put,different] using image.rootStored)
      (by simp [WordWrites.write,StoreWord.put])
    exact ⟨StoreWord.execute source destination expression _ reference destinationRead valueRead mapped,retained⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.reference_store
