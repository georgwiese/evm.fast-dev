import InitECandidate.Solver.MutableTable.GetSizedOrigin
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A current value array satisfies a pure ownership/resource predicate at
every bounded slot, including unused zeroed slots. No logical keys or
future lookup outcome are assumed. -/
def ValuesHave (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity : BitVec 64) (property : BitVec 64 → Prop) : Prop :=
  ∀ slot : BitVec 64,slot.toNat<capacity.toNat → ∀ value : BitVec 64,source.memory (vals+slot*8#64)=.word value → property value

theorem ValueOrigin.value_property (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity flag value : BitVec 64)
    (property : BitVec 64 → Prop) (origin : ValueOrigin source vals capacity flag value) (values : ValuesHave source vals capacity property) :
    flag=0#64 ∨ property value := by
  rcases origin with absent | ⟨slot,inside,stored⟩
  · exact Or.inl absent
  · exact Or.inr (values slot inside value stored)

theorem ValueOrigin.present_property (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity flag value : BitVec 64)
    (property : BitVec 64 → Prop) (origin : ValueOrigin source vals capacity flag value) (values : ValuesHave source vals capacity property)
    (present : flag=1#64) : property value := by
  rcases origin.value_property source vals capacity flag value property values with absent | owned
  · exact ((by decide : (1#64 : BitVec 64)≠0#64) (present.symm.trans absent)).elim
  · exact owned

theorem ValuesHave.of_agreement (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity : BitVec 64)
    (property : BitVec 64 → Prop) (values : ValuesHave source vals capacity property)
    (agree : ∀ slot : BitVec 64,slot.toNat<capacity.toNat → target.memory (vals+slot*8#64)=source.memory (vals+slot*8#64)) :
    ValuesHave target vals capacity property := by
  intro slot inside value stored
  apply values slot inside value
  rw [←agree slot inside]
  exact stored

theorem ValuesHave.mono (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity : BitVec 64)
    (property nextProperty : BitVec 64 → Prop) (values : ValuesHave source vals capacity property)
    (implication : ∀ value,property value → nextProperty value) : ValuesHave source vals capacity nextProperty :=
  fun slot inside value stored=>implication value (values slot inside value stored)

theorem ValuesHave.zeroed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity : BitVec 64)
    (property : BitVec 64 → Prop) (zero : property 0#64)
    (cleared : ∀ slot : BitVec 64,slot.toNat<capacity.toNat → source.memory (vals+slot*8#64)=.word 0#64) : ValuesHave source vals capacity property := by
  intro slot inside value stored
  have same : value=0#64 := by simpa only [HolWordLab.word.injEq] using stored.symm.trans (cleared slot inside)
  rw [same]
  exact zero

/-- A real table value write retains any pure value predicate satisfied by
the incoming array and the actual newly stored word. -/
theorem ValuesHave.word_update (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity destination value : BitVec 64)
    (property : BitVec 64 → Prop) (values : ValuesHave source vals capacity property) (owned : property value) :
    ValuesHave {source with memory:=StoreWord.put source.memory destination value} vals capacity property := by
  intro slot inside word stored
  by_cases same : vals+slot*8#64=destination
  · have wordEq : value=word := by simpa only [StoreWord.put,if_pos same,HolWordLab.word.injEq] using stored
    rw [←wordEq]
    exact owned
  · apply values slot inside word
    simpa only [StoreWord.put,if_neg same] using stored

/-- A checked relocation/reinsertion can introduce only zeros, the new
setter value or words loaded from its original bounded value array. -/
def ValuesFrom (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (oldVals oldCapacity vals capacity added : BitVec 64) : Prop :=
  ∀ slot : BitVec 64,slot.toNat<capacity.toNat → ∀ value : BitVec 64,target.memory (vals+slot*8#64)=.word value →
    value=0#64 ∨ value=added ∨ ∃ original : BitVec 64,original.toNat<oldCapacity.toNat ∧ source.memory (oldVals+original*8#64)=.word value

theorem ValuesHave.of_sources (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (oldVals oldCapacity vals capacity added : BitVec 64)
    (property : BitVec 64 → Prop) (values : ValuesHave source oldVals oldCapacity property) (zero : property 0#64) (newValue : property added)
    (origins : ValuesFrom source target oldVals oldCapacity vals capacity added) : ValuesHave target vals capacity property := by
  intro slot inside value stored
  rcases origins slot inside value stored with empty | fresh | ⟨original,prior,read⟩
  · rw [empty]; exact zero
  · rw [fresh]; exact newValue
  · exact values original prior value read

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.ValueOrigin.value_property
#print axioms InitECandidate.Solver.MutableTable.Get.ValueOrigin.present_property
#print axioms InitECandidate.Solver.MutableTable.Get.ValuesHave.of_agreement
#print axioms InitECandidate.Solver.MutableTable.Get.ValuesHave.mono
#print axioms InitECandidate.Solver.MutableTable.Get.ValuesHave.zeroed
#print axioms InitECandidate.Solver.MutableTable.Get.ValuesHave.word_update
#print axioms InitECandidate.Solver.MutableTable.Get.ValuesHave.of_sources
