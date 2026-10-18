import InitECandidate.Solver.GasBudget.JournalRecordGeometry
import InitECandidate.Solver.MutableTable.FamilyExtend

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout

def Entry.lift {ι : Type} (entry : Entry ι) : Entry (Option ι) := ⟨some entry.writer, entry.key, entry.flag, entry.value⟩

/-- Adding a fresh table after the old cursor preserves every reserved
journal slot, including unused slots, under the extended identity family. -/
theorem Zone.extend {ι : Type} {objects : ι → TableFamily.Object} {base cap cursor nextCursor : Nat}
    (zone : Zone objects base cap cursor) (fresh : TableFamily.Object) (valid : Valid fresh.kind fresh.plan)
    (afterJournal : cursor ≤ fresh.floor) (lower : ∀ pool, fresh.floor ≤ fresh.plan.base pool) (forward : cursor ≤ nextCursor) :
    Zone (TableFamily.extend objects fresh) base cap nextCursor := by
  refine ⟨zone.valid, by have earlier := zone.earlier; omega, ?_⟩
  intro index inside field table
  cases table with
  | some table => exact zone.separate index inside field table
  | none =>
    apply TableFootprint.Outside.of_regions fresh.kind fresh.plan valid
    intro pool
    left
    rw [entry_number base cap index field zone.valid inside]
    have fieldBound := field.isLt
    have earlier := zone.earlier
    have after := lower pool
    omega

/-- A new table changes no old record meaning. The saved identities lift
through Option.some, and its full reservation supplies new-owner separation. -/
theorem Image.extend {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {objects : ι → TableFamily.Object}
    {base cap count cursor : Nat} {entries : Nat → Entry ι} (image : Image source objects base count entries)
    (fresh : TableFamily.Object) (zone : Zone (TableFamily.extend objects fresh) base cap cursor) (bounded : count ≤ cap) :
    Image source (TableFamily.extend objects fresh) base count (fun index => (entries index).lift) := by
  constructor
  · exact image.mapped
  · intro index inside field
    exact image.words index inside field
  · intro index inside field table
    exact zone.separate index (by omega) field table
  · exact image.queryFits
  · exact image.queryMapped

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.Zone.extend
#print axioms InitECandidate.Solver.GasBudget.Journal.Image.extend
