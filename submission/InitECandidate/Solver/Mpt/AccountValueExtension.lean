import InitECandidate.Solver.MutableTable.FamilyValues
import InitECandidate.Solver.GasBudget.JournalEntryValues
import InitECandidate.Solver.Mpt.AccountRegistryExtension

namespace InitECandidate.Solver.Mpt.AccountValueExtension
open Flapjack PanSemStateFiniteExact MutableTable GasBudget

def added {ι : Type} (property : ι → BitVec 64 → Prop) (writer : ι) (fresh : BitVec 64) (index : ι) (value : BitVec 64) : Prop :=
  property index value ∨ index = writer ∧ value = fresh

theorem live_values {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (writer : ι) (fresh : BitVec 64) :
    TableFamily.ValuesHave source objects (added property writer fresh) :=
  values.mono source objects property (added property writer fresh) (fun _ _ prior => Or.inl prior)

theorem saved_values {ι : Type} (entries : Nat → Journal.Entry ι) (count : Nat)
    (property : ι → BitVec 64 → Prop) (values : Journal.EntryValues entries count property) (writer : ι) (fresh : BitVec 64) :
    Journal.EntryValues entries count (added property writer fresh) :=
  values.mono entries count property (added property writer fresh) (fun _ _ prior => Or.inl prior)

theorem other {ι : Type} (property : ι → BitVec 64 → Prop) (writer index : ι) (fresh value : BitVec 64) (different : index ≠ writer) :
    added property writer fresh index value ↔ property index value := by simp [added,different]

/-- A freshly registered copy is added to a publication predicate using
its actual registry membership. Old occupied and undo values remain owned. -/
theorem known {ι : Type} (property : ι → BitVec 64 → Prop) (writer : ι) (fresh : BitVec 64)
    (accounts next : List (BitVec 64)) (cursor : Nat) (extension : AccountDecode.Registry.Extension accounts next cursor)
    (oldKnown : ∀ value,property writer value → AccountDecode.Registry.Known accounts value)
    (freshMember : fresh ∈ next) : ∀ value,added property writer fresh writer value → AccountDecode.Registry.Known next value := by
  intro value owned
  rcases owned with old | freshEq
  · exact extension.known value (oldKnown value old)
  · rw [freshEq.2]
    exact Or.inr freshMember

end InitECandidate.Solver.Mpt.AccountValueExtension

#print axioms InitECandidate.Solver.Mpt.AccountValueExtension.live_values
#print axioms InitECandidate.Solver.Mpt.AccountValueExtension.saved_values
#print axioms InitECandidate.Solver.Mpt.AccountValueExtension.other
#print axioms InitECandidate.Solver.Mpt.AccountValueExtension.known
