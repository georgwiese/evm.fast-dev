import InitECandidate.Solver.GasBudget.JournalImage

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack

/-- A live undo record owns its old value when the original lookup found
an occupied key. Absent records impose no condition on their unused value. -/
def EntryValues {ι : Type} (entries : Nat → Entry ι) (count : Nat) (property : ι → BitVec 64 → Prop) : Prop :=
  ∀ index,index<count → (entries index).flag≠0#64 → property (entries index).writer (entries index).value

theorem EntryValues.empty {ι : Type} (entries : Nat → Entry ι) (property : ι → BitVec 64 → Prop) : EntryValues entries 0 property := by
  intro index inside; omega

theorem EntryValues.restrict {ι : Type} (entries : Nat → Entry ι) (count next : Nat) (property : ι → BitVec 64 → Prop)
    (values : EntryValues entries count property) (smaller : next≤count) : EntryValues entries next property :=
  fun index inside present=>values index (by omega) present

theorem EntryValues.append {ι : Type} (entries : Nat → Entry ι) (count : Nat) (property : ι → BitVec 64 → Prop)
    (values : EntryValues entries count property) (entry : Entry ι) (owned : entry.flag=0#64 ∨ property entry.writer entry.value) :
    EntryValues (Function.update entries count entry) (count+1) property := by
  intro index inside present
  by_cases same : index=count
  · subst index
    rw [Function.update_self] at present ⊢
    rcases owned with absent | found
    · exact (present absent).elim
    · exact found
  · rw [Function.update_of_ne same] at present ⊢
    exact values index (by omega) present

theorem EntryValues.mono {ι : Type} (entries : Nat → Entry ι) (count : Nat) (property next : ι → BitVec 64 → Prop)
    (values : EntryValues entries count property) (implication : ∀ index value,property index value → next index value) : EntryValues entries count next :=
  fun index inside present=>implication _ _ (values index inside present)

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.EntryValues.empty
#print axioms InitECandidate.Solver.GasBudget.Journal.EntryValues.restrict
#print axioms InitECandidate.Solver.GasBudget.Journal.EntryValues.append
#print axioms InitECandidate.Solver.GasBudget.Journal.EntryValues.mono
