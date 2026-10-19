import InitECandidate.Solver.MutableTable.ValueProperty

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Current ownership for physically occupied slots only. Original table
allocation clears occupancy and leaves unused value words unrestricted. -/
def OccupiedValuesHave (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity : BitVec 64)
    (slots : List Nat) (property : BitVec 64 → Prop) : Prop :=
  ∀ slot : BitVec 64,slot.toNat<capacity.toNat → slot.toNat∈slots → ∀ value : BitVec 64,source.memory (vals+slot*8#64)=.word value → property value

theorem OccupiedValuesHave.empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity : BitVec 64) (property : BitVec 64 → Prop) :
    OccupiedValuesHave source vals capacity [] property := by intro slot inside member; cases member

/-- The actual lookup's selected occupied slot, rather than an assumption
about unused array memory, supplies the returned value's ownership. -/
theorem ValueOrigin.occupied_property (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity flag value : BitVec 64)
    (slots : List Nat) (property : BitVec 64 → Prop)
    (origin : ValueOrigin source vals capacity flag value (fun slot=>slot.toNat∈slots))
    (values : OccupiedValuesHave source vals capacity slots property) : flag=0#64 ∨ property value := by
  rcases origin with absent | ⟨slot,inside,member,stored⟩
  · exact Or.inl absent
  · exact Or.inr (values slot inside member value stored)

theorem ValueOrigin.occupied_present (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity flag value : BitVec 64)
    (slots : List Nat) (property : BitVec 64 → Prop)
    (origin : ValueOrigin source vals capacity flag value (fun slot=>slot.toNat∈slots))
    (values : OccupiedValuesHave source vals capacity slots property) (present : flag≠0#64) : property value := by
  rcases origin.occupied_property source vals capacity flag value slots property values with absent | owned
  · exact (present absent).elim
  · exact owned

theorem OccupiedValuesHave.of_agreement (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity : BitVec 64)
    (slots : List Nat) (property : BitVec 64 → Prop) (values : OccupiedValuesHave source vals capacity slots property)
    (agree : ∀ slot : BitVec 64,slot.toNat<capacity.toNat → slot.toNat∈slots → target.memory (vals+slot*8#64)=source.memory (vals+slot*8#64)) :
    OccupiedValuesHave target vals capacity slots property := by
  intro slot inside member value stored
  apply values slot inside member value
  rw [←agree slot inside member]
  exact stored

theorem OccupiedValuesHave.mono (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity : BitVec 64) (slots : List Nat)
    (property nextProperty : BitVec 64 → Prop) (values : OccupiedValuesHave source vals capacity slots property)
    (implication : ∀ value,property value → nextProperty value) : OccupiedValuesHave source vals capacity slots nextProperty :=
  fun slot inside member value stored=>implication value (values slot inside member value stored)

theorem OccupiedValuesHave.word_update (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity destination added : BitVec 64)
    (slots : List Nat) (property : BitVec 64 → Prop) (values : OccupiedValuesHave source vals capacity slots property) (owned : property added) :
    OccupiedValuesHave {source with memory:=StoreWord.put source.memory destination added} vals capacity slots property := by
  intro slot inside member value stored
  by_cases same : vals+slot*8#64=destination
  · have wordEq : added=value := by simpa only [StoreWord.put,if_pos same,HolWordLab.word.injEq] using stored
    rw [←wordEq]; exact owned
  · apply values slot inside member value
    simpa only [StoreWord.put,if_neg same] using stored

theorem OccupiedValuesHave.append_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity index added : BitVec 64)
    (slots : List Nat) (property : BitVec 64 → Prop) (values : OccupiedValuesHave source vals capacity slots property) (owned : property added) :
    OccupiedValuesHave {source with memory:=StoreWord.put source.memory (vals+index*8#64) added} vals capacity (slots++[index.toNat]) property := by
  intro slot inside member value stored
  by_cases same : vals+slot*8#64=vals+index*8#64
  · have wordEq : added=value := by simpa only [StoreWord.put,if_pos same,HolWordLab.word.injEq] using stored
    rw [←wordEq]; exact owned
  · have old : slot.toNat∈slots := by
      rcases List.mem_append.mp member with old | fresh
      · exact old
      · have number : slot.toNat=index.toNat := by simpa using fresh
        have equal := BitVec.eq_of_toNat_eq number
        exact (same (by rw [equal])).elim
    apply values slot inside old value
    simpa only [StoreWord.put,if_neg same] using stored

/-- Origins for actual reinserted occupied slots. Unused destination words
are unrestricted and need no zero initialization assumption. -/
def OccupiedValuesFrom (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (oldVals oldCapacity vals capacity added : BitVec 64)
    (oldSlots slots : List Nat) : Prop :=
  ∀ slot : BitVec 64,slot.toNat<capacity.toNat → slot.toNat∈slots → ∀ value : BitVec 64,target.memory (vals+slot*8#64)=.word value →
    value=added ∨ ∃ original : BitVec 64,original.toNat<oldCapacity.toNat ∧ original.toNat∈oldSlots ∧ source.memory (oldVals+original*8#64)=.word value

theorem OccupiedValuesHave.of_sources (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (oldVals oldCapacity vals capacity added : BitVec 64)
    (oldSlots slots : List Nat) (property : BitVec 64 → Prop) (values : OccupiedValuesHave source oldVals oldCapacity oldSlots property) (newValue : property added)
    (origins : OccupiedValuesFrom source target oldVals oldCapacity vals capacity added oldSlots slots) : OccupiedValuesHave target vals capacity slots property := by
  intro slot inside member value stored
  rcases origins slot inside member value stored with fresh | ⟨original,prior,occupied,read⟩
  · rw [fresh]; exact newValue
  · exact values original prior occupied value read

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.OccupiedValuesHave.empty
#print axioms InitECandidate.Solver.MutableTable.Get.ValueOrigin.occupied_property
#print axioms InitECandidate.Solver.MutableTable.Get.ValueOrigin.occupied_present
#print axioms InitECandidate.Solver.MutableTable.Get.OccupiedValuesHave.of_agreement
#print axioms InitECandidate.Solver.MutableTable.Get.OccupiedValuesHave.mono
#print axioms InitECandidate.Solver.MutableTable.Get.OccupiedValuesHave.word_update
#print axioms InitECandidate.Solver.MutableTable.Get.OccupiedValuesHave.append_word
#print axioms InitECandidate.Solver.MutableTable.Get.OccupiedValuesHave.of_sources
