import InitECandidate.Solver.MutableTable.FamilyValues
import InitECandidate.Solver.MutableTable.MemoryModelPoolFrame

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact NaturalLayout

/-- Concrete agreement on live pools retains the occupied values. -/
theorem ValuesHave.of_pools {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → Object) (cursor : Nat) (family : Model source cursor objects)
    (property : ι → BitVec 64 → Prop) (values : ValuesHave source objects property)
    (pools : ∀ index,MemoryModel.PoolFrame source.memory target.memory (objects index).kind (objects index).plan) :
    ValuesHave target objects property := by
  apply values.of_agreement source target objects property
  intro index slot inside occupied
  have valid := (family.tables index).valid
  have capNumber : (BitVec.ofNat 64 (objects index).plan.capacity).toNat=(objects index).plan.capacity := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (capacity_small (objects index).kind _ valid)]
  rw [capNumber] at inside
  rw [scaled_cell]
  exact pools index .values _ (word_offset_inside (objects index).kind _ .values slot.toNat (Or.inl rfl) inside)

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.ValuesHave.of_pools
