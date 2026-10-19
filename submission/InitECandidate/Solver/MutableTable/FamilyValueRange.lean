import InitECandidate.Solver.MutableTable.FamilyValues

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact NaturalLayout

/-- A real earlier-word frame retains occupied values in every current
table pool. Unused array words remain unrestricted. -/
theorem ValuesHave.of_range {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cutoff cursor : Nat) (objects : ι → Object) (property : ι → BitVec 64 → Prop)
    (family : Model source cursor objects) (values : ValuesHave source objects property)
    (floors : ∀ index,cutoff≤(objects index).floor)
    (agree : ∀ address : BitVec 64,cutoff≤address.toNat → address.toNat<cursor → target.memory address=source.memory address) :
    ValuesHave target objects property := by
  apply values.of_agreement source target objects property
  intro index slot inside member
  have table := family.tables index
  have capNumber : (BitVec.ofNat 64 (objects index).plan.capacity).toNat=(objects index).plan.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity_small (objects index).kind _ table.valid)]
  rw [capNumber] at inside
  have extent := word_offset_inside (objects index).kind (objects index).plan .values slot.toNat (Or.inl rfl) inside
  rw [scaled_cell]
  apply agree
  · rw [number (objects index).kind _ table.valid .values _ extent]
    have lower := table.lower .values
    have floor := floors index
    omega
  · rw [number (objects index).kind _ table.valid .values _ extent]
    have earlier := table.earlier .values
    omega

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.ValuesHave.of_range
