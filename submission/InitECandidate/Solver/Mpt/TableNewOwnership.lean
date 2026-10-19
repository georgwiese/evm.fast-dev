import InitECandidate.Solver.GasBudget.JournalTableNew
import InitECandidate.Solver.GasBudget.JournalEntryValues
import InitECandidate.Solver.MutableTable.FamilyValuePools
import InitECandidate.Solver.Mpt.AccountRegistry

namespace InitECandidate.Solver.Mpt.TableNewOwnership
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout GasBudget

def liftProperty {ι : Type} (property : ι → BitVec 64 → Prop) (fresh : BitVec 64 → Prop) : Option ι → BitVec 64 → Prop
  | none => fresh
  | some index => property index

/-- The original constructor writes only its fresh reservation. Old occupied
values, undo values and registered accounts survive the real identity extension. -/
theorem models {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (cursor cutoff capacity : Nat) (kind : KeyHash.Kind) (objects : ι → TableFamily.Object)
    (family : TableFamily.Model source cursor objects)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (entries : Nat → Journal.Entry ι) (count : Nat) (savedValues : Journal.EntryValues entries count property)
    (freshProperty : BitVec 64 → Prop) (valid : Valid kind (fresh kind cursor capacity)) :
    let target := TableRuntime.callState source name kind cursor capacity
    let next := TableFamily.extend objects (Journal.newObject kind cursor capacity)
    AccountDecode.Registry target cutoff (freshEnd kind cursor capacity) next accounts ∧
      TableFamily.ValuesHave target next (liftProperty property freshProperty) ∧
      Journal.EntryValues (fun index => (entries index).lift) count (liftProperty property freshProperty) ∧
      (∀ query : BitVec 64, query.toNat < cursor → TableFamily.Outside objects query →
        TableFamily.Outside next query ∧ target.memory query = source.memory query) := by
  let target := TableRuntime.callState source name kind cursor capacity
  let next := TableFamily.extend objects (Journal.newObject kind cursor capacity)
  have forward : cursor ≤ freshEnd kind cursor capacity := by dsimp only [freshEnd]; omega
  have earlierWords (query : BitVec 64) (earlier : query.toNat < cursor) : target.memory query = source.memory query :=
    TableRuntime.caller_memory_away source name kind cursor capacity valid query (Or.inl earlier)
  have outsideNext (query : BitVec 64) (earlier : query.toNat < cursor) (outside : TableFamily.Outside objects query) : TableFamily.Outside next query := by
    intro index
    cases index with
    | some index => exact outside index
    | none =>
      apply TableFootprint.Outside.of_regions kind (fresh kind cursor capacity) valid
      intro pool
      left
      have lower := (fresh_bounds kind cursor capacity pool).1
      omega
  have nextRegistry : AccountDecode.Registry target cutoff (freshEnd kind cursor capacity) next accounts := by
    refine ⟨registry.distinct,?_,registry.above,?_,registry.separated,?_⟩
    · intro account member
      obtain ⟨image⟩ := registry.images account member
      have before := registry.before account member
      exact ⟨AccountDecode.Image.of_agreement source target account image rfl
        (earlierWords _ (by rw [image.output.slot_number account 40 (by decide)]; omega))
        (earlierWords _ (by rw [image.output.slot_number account 48 (by decide)]; omega))⟩
    · intro account member
      exact Nat.le_trans (registry.before account member) forward
    · intro account member offset inside
      obtain ⟨image⟩ := registry.images account member
      have before := registry.before account member
      apply outsideNext _ _ (registry.objectOutside account member offset inside)
      rw [image.output.slot_number account offset inside]
      omega
  have pools : ∀ index,MemoryModel.PoolFrame source.memory target.memory (objects index).kind (objects index).plan := by
    intro index pool offset inside
    apply earlierWords
    rw [NaturalLayout.number (objects index).kind (objects index).plan (family.tables index).valid pool offset inside]
    have before := (family.tables index).earlier pool
    omega
  have oldValues := values.of_pools source target objects cursor family property pools
  refine ⟨nextRegistry,?_,?_,fun query earlier outside => ⟨outsideNext query earlier outside,earlierWords query earlier⟩⟩
  · intro index
    cases index with
    | some index => exact oldValues index
    | none => exact Get.OccupiedValuesHave.empty _ _ _ _
  · intro index inside present
    exact savedValues index inside present

end InitECandidate.Solver.Mpt.TableNewOwnership

#print axioms InitECandidate.Solver.Mpt.TableNewOwnership.models
