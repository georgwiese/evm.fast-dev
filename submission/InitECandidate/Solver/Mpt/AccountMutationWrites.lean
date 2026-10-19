import InitECandidate.Solver.Mpt.AccountRegistryWrites
import InitECandidate.Solver.GasBudget.JournalRecordGeometry

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget

theorem object_writes_window (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account : BitVec 64) (image : Image source account)
    (writes : List (BitVec 64 × BitVec 64))
    (contained : ∀ entry ∈ writes,∃ offset : Nat,offset < 56 ∧ entry.1 = account + BitVec.ofNat 64 offset) :
    Rlp.Slices.Window source {source with memory := WordWrites.write source.memory writes} account.toNat (account.toNat + 56) := by
  intro query away
  apply WordWrites.write_away
  intro found
  obtain ⟨entry,member,same⟩ := List.mem_map.mp found
  obtain ⟨offset,inside,address⟩ := contained entry member
  have numbers := congrArg BitVec.toNat (address.symm.trans same)
  rw [image.output.slot_number account offset inside] at numbers
  rcases away with before | after <;> omega

theorem journal_after_object_writes {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → TableFamily.Object) (base cap count cursor : Nat) (entries : Nat → Journal.Entry ι)
    (journal : Journal.Image source objects base count entries) (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (account : BitVec 64) (image : Image source account) (apart : account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (writes : List (BitVec 64 × BitVec 64))
    (contained : ∀ entry ∈ writes,∃ offset : Nat,offset < 56 ∧ entry.1 = account + BitVec.ofNat 64 offset) :
    Journal.Image {source with memory := WordWrites.write source.memory writes} objects base count entries := by
  have window := object_writes_window source account image writes contained
  apply journal.transfer (target := {source with memory := WordWrites.write source.memory writes}) rfl (fun _ => rfl) (fun _ => rfl) _ journal.separate
  intro index inside field
  have number := Journal.entry_number base cap index field zone.valid (by omega)
  have fieldBound := field.isLt
  apply window
  rcases apart with before | after
  · right; rw [number]; omega
  · left; rw [number]; omega

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.object_writes_window
#print axioms InitECandidate.Solver.Mpt.AccountDecode.journal_after_object_writes
