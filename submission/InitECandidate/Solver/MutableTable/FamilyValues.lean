import InitECandidate.Solver.MutableTable.TableFamily
import InitECandidate.Solver.MutableTable.OccupiedValueFields

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact NaturalLayout

/-- Each live table has its own predicate on actual occupied values. -/
def ValuesHave {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → Object) (property : ι → BitVec 64 → Prop) : Prop :=
  ∀ index, Get.OccupiedValuesHave source (cell (objects index).plan .values 0)
    (BitVec.ofNat 64 (objects index).plan.capacity) (objects index).slots (property index)

theorem ValuesHave.empty {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → Object) (property : ι → BitVec 64 → Prop)
    (empty : ∀ index, (objects index).slots=[]) : ValuesHave source objects property := by
  intro index
  rw [empty index]
  exact Get.OccupiedValuesHave.empty _ _ _ _

theorem ValuesHave.mono {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → Object) (property nextProperty : ι → BitVec 64 → Prop)
    (values : ValuesHave source objects property)
    (implication : ∀ index value,property index value → nextProperty index value) : ValuesHave source objects nextProperty := by
  intro index
  exact (values index).mono source _ _ _ _ _ (implication index)

theorem ValuesHave.of_agreement {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → Object) (property : ι → BitVec 64 → Prop) (values : ValuesHave source objects property)
    (agree : ∀ index,∀ slot : BitVec 64,slot.toNat<(BitVec.ofNat 64 (objects index).plan.capacity).toNat → slot.toNat∈(objects index).slots →
      target.memory (cell (objects index).plan .values 0+slot*8#64)=source.memory (cell (objects index).plan .values 0+slot*8#64)) :
    ValuesHave target objects property := by
  intro index
  exact (values index).of_agreement source target _ _ _ _ (agree index)

theorem ValuesHave.of_memory {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → Object) (property : ι → BitVec 64 → Prop) (values : ValuesHave source objects property)
    (same : source.memory=target.memory) : ValuesHave target objects property := by
  intro index
  exact (values index).of_memory source target _ _ _ _ same

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.ValuesHave.empty
#print axioms InitECandidate.Solver.MutableTable.TableFamily.ValuesHave.mono
#print axioms InitECandidate.Solver.MutableTable.TableFamily.ValuesHave.of_agreement
#print axioms InitECandidate.Solver.MutableTable.TableFamily.ValuesHave.of_memory
