import Flapjack.Compiler.Backend.Semantics.StackSem.Inst

namespace InitECandidate.Solver.GuestWork.ZeroMemory
open Flapjack

/-- Every existing word remains a word with no larger unsigned value. This
allows overlap when preserving an upper bound on a saved length. -/
def Below {width : Nat} [NeZero width] (after before : BitVec width → WordLocW width) : Prop :=
  ∀ address value, before address = .word value →
    ∃ next, after address = .word next ∧ next.toNat ≤ value.toNat

theorem Below.refl {width : Nat} [NeZero width] (memory : BitVec width → WordLocW width) : Below memory memory := by
  intro address value found
  exact ⟨value, found, Nat.le_refl _⟩

theorem Below.trans {width : Nat} [NeZero width] {first middle last : BitVec width → WordLocW width}
    (a : Below middle first) (b : Below last middle) : Below last first := by
  intro address value found
  obtain ⟨next, nextFound, nextLe⟩ := a address value found
  obtain ⟨final, finalFound, finalLe⟩ := b address next nextFound
  exact ⟨final, finalFound, Nat.le_trans finalLe nextLe⟩

theorem wordUpdate {width : Nat} [NeZero width] (memory : BitVec width → WordLocW width)
    (address : BitVec width) :
    Below (fun key => if key = address then .word 0 else memory key) memory := by
  intro key value found
  by_cases same : key = address
  · exact ⟨0, by simp [same], by simp⟩
  · exact ⟨value, by simpa [same] using found, Nat.le_refl _⟩

theorem zeroByte_le {width : Nat} [NeZero width] (address value : BitVec width) (bigEndian : Bool) :
    (setByteHOL8 address 0#8 value bigEndian).toNat ≤ value.toNat := by
  simp only [setByteHOL8, BitVec.setWidth_zero, BitVec.zero_shiftLeft,
    BitVec.or_zero, BitVec.toNat_and]
  exact Nat.and_le_left

theorem byteStore {width : Nat} [NeZero width]
    (memory next : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bigEndian : Bool) (address : BitVec width)
    (execution : memStoreByteAuxExact memory domain bigEndian address 0#8 = some next) :
    Below next memory := by
  unfold memStoreByteAuxExact at execution
  cases found : memory (riscvByteAlignHOL address) with
  | loc label offset => simp [found] at execution
  | word value =>
    simp only [found] at execution
    split at execution
    · simp only [Option.some.injEq] at execution
      subst next
      intro key original originalFound
      by_cases same : key = riscvByteAlignHOL address
      · subst key
        rw [found] at originalFound
        cases originalFound
        exact ⟨setByteHOL8 address 0#8 value bigEndian, by simp, zeroByte_le address value bigEndian⟩
      · exact ⟨original, by simpa [same] using originalFound, Nat.le_refl _⟩
    · simp at execution

theorem Below.bound {width : Nat} [NeZero width] {before after : BitVec width → WordLocW width}
    (below : Below after before) (address : BitVec width) (maximum : Nat)
    (bounded : ∃ value, before address = .word value ∧ value.toNat ≤ maximum) :
    ∃ value, after address = .word value ∧ value.toNat ≤ maximum := by
  obtain ⟨value, found, small⟩ := bounded
  obtain ⟨next, nextFound, nextSmall⟩ := below address value found
  exact ⟨next, nextFound, Nat.le_trans nextSmall small⟩

end InitECandidate.Solver.GuestWork.ZeroMemory
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Below.refl
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Below.trans
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.wordUpdate
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.zeroByte_le
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.byteStore
#print axioms InitECandidate.Solver.GuestWork.ZeroMemory.Below.bound
