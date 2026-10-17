import InitECandidate.Solver.WitnessRadix.TableState
import InitECandidate.Solver.WitnessRadix.LayoutCells

namespace InitECandidate.Solver.WitnessRadix.TableNew
open BackingLayout

def beforeSites : List Address := [(.header, 0), (.header, 8), (.header, 16), (.header, 24), (.header, 32), (.header, 40)]
def afterSites : List Address := [(.header, 48), (.header, 56), (.header, 64)]

theorem before_cells (plan : AllocatedLayout.Plan) :
    (beforeWrites plan).map Prod.fst = beforeSites.map (address (AllocatedLayout.layout plan)) := by
  simp [beforeWrites, beforeSites, address, cell, base, AllocatedLayout.layout, byteAddress]

theorem after_cells (plan : AllocatedLayout.Plan) :
    (afterWrites plan).map Prod.fst = afterSites.map (address (AllocatedLayout.layout plan)) := by
  simp [afterWrites, afterSites, address, cell, base, AllocatedLayout.layout, byteAddress]

theorem before_bounds (plan : AllocatedLayout.Plan) :
    ∀ entry ∈ beforeSites, entry.2 < size (AllocatedLayout.layout plan) entry.1 := by
  intro entry member
  simp only [beforeSites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> change _ < 72 <;> decide

theorem after_bounds (plan : AllocatedLayout.Plan) :
    ∀ entry ∈ afterSites, entry.2 < size (AllocatedLayout.layout plan) entry.1 := by
  intro entry member
  simp only [afterSites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> change _ < 72 <;> decide

theorem before_distinct (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) :
    ((beforeWrites plan).map Prod.fst).Nodup := by
  rw [before_cells]
  exact addresses_nodup _ (AllocatedLayout.valid plan ready) beforeSites (before_bounds plan) (by decide)

theorem after_distinct (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) :
    ((afterWrites plan).map Prod.fst).Nodup := by
  rw [after_cells]
  exact addresses_nodup _ (AllocatedLayout.valid plan ready) afterSites (after_bounds plan) (by decide)

theorem after_away (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (offset : Nat) (before : offset < 48) :
    cell (AllocatedLayout.layout plan) .header offset ∉ (afterWrites plan).map Prod.fst := by
  rw [after_cells]
  intro member
  obtain ⟨other, otherMember, same⟩ := List.mem_map.mp member
  have equal := address_injective _ (AllocatedLayout.valid plan ready) other (.header, offset)
    (after_bounds plan other otherMember) (by change offset < 72; omega) same
  have absent : (.header, offset) ∉ afterSites := by simp [afterSites]; omega
  exact absent (equal ▸ otherMember)

theorem header_number (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (offset : Nat) (inside : offset < 72) :
    (cell (AllocatedLayout.layout plan) .header offset).toNat = plan.table + offset := by
  have fits := ready.fits
  have tableSmall : plan.table < 2 ^ 64 := by omega
  change (byteAddress (BitVec.ofNat 64 plan.table) offset).toNat = _
  have number : (BitVec.ofNat 64 plan.table).toNat = plan.table := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt tableSmall]
  rw [byteAddress_toNat _ _ (by rw [number]; omega), number]

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.before_distinct
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.after_distinct
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.after_away
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.header_number
