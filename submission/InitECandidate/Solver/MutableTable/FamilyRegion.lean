import InitECandidate.Solver.MutableTable.FamilyMemoryFrame
import InitECandidate.Solver.MutableTable.FamilyExtend
import InitECandidate.Solver.MutableTable.MemoryRegion
import InitECandidate.Solver.MutableTable.TableFootprint

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- A persistent record may sit between old and later table pools. -/
def ApartRegion {ι : Type} (objects : ι → Object) (region : MemoryRegion.Region) : Prop :=
  ∀ index pool, (objects index).plan.base pool + size (objects index).kind (objects index).plan pool ≤ region.start ∨
    region.start + region.length ≤ (objects index).plan.base pool

theorem Model.before_region {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) (region : MemoryRegion.Region) (afterTables : cursor ≤ region.start) : ApartRegion objects region := by
  intro index pool
  exact Or.inl (Nat.le_trans ((family.tables index).earlier pool) afterTables)

theorem ApartRegion.extend {ι : Type} {objects : ι → Object} {region : MemoryRegion.Region}
    (apart : ApartRegion objects region) (fresh : Object) (afterRegion : region.start + region.length ≤ fresh.floor)
    (lower : ∀ pool, fresh.floor ≤ fresh.plan.base pool) : ApartRegion (extend objects fresh) region := by
  intro index pool
  cases index with
  | some index => exact apart index pool
  | none => exact Or.inr (Nat.le_trans afterRegion (lower pool))

theorem ApartRegion.outside {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) (region : MemoryRegion.Region) (valid : MemoryRegion.Valid region)
    (apart : ApartRegion objects region) (offset : Nat) (inside : offset < region.length) (index : ι) :
    TableFootprint.Outside (objects index).kind (objects index).plan (MemoryRegion.address region offset) := by
  apply TableFootprint.Outside.of_regions _ _ (family.tables index).valid
  intro pool
  rw [MemoryRegion.address_number region valid offset (by omega)]
  rcases apart index pool with before | afterRegion
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

/-- A real word in a separated persistent record can change without
invalidating any header, binary used array or order/position representation. -/
theorem Model.write_region {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) (region : MemoryRegion.Region) (valid : MemoryRegion.Valid region)
    (apart : ApartRegion objects region) (offset : Nat) (inside : offset < region.length) (word : BitVec 64) :
    Model {source with memory := StoreWord.put source.memory (MemoryRegion.address region offset) word} cursor objects := by
  apply family.of_pools (target := {source with memory := StoreWord.put source.memory (MemoryRegion.address region offset) word}) rfl rfl rfl
  intro index pool current bounded
  exact if_neg (Ne.symm (apart.outside family region valid offset inside index pool current bounded))

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.before_region
#print axioms InitECandidate.Solver.MutableTable.TableFamily.ApartRegion.extend
#print axioms InitECandidate.Solver.MutableTable.TableFamily.ApartRegion.outside
#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.write_region
