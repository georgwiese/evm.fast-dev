import InitECandidate.Solver.GasBudget.JournalImage

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Ownership of all journal slots, including unused slots needed by the
next append. This is stronger than ownership of the current live prefix. -/
structure Zone {ι : Type} (objects : ι → TableFamily.Object) (base cap cursor : Nat) : Prop where
  valid : MemoryRegion.Valid ⟨base, 32 * cap⟩
  earlier : base + 32 * cap ≤ cursor
  separate : ∀ index < cap, ∀ field table, TableFootprint.Outside (objects table).kind (objects table).plan (entryAddress base index field)

theorem Zone.mapped {ι : Type} {objects : ι → TableFamily.Object} {base cap cursor : Nat}
    (zone : Zone objects base cap cursor) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (domain : source.memaddrs = InitE.ordinaryDomain) (index : Nat) (inside : index < cap) (field : Fin 4) :
    source.memaddrs (entryAddress base index field) := by
  have fieldBound := field.isLt
  have lower := zone.valid.lower
  have upper := zone.valid.upper
  have aligned := zone.valid.aligned
  change 2701131776 ≤ base at lower
  change base + 32 * cap ≤ 33806089496 at upper
  change base % 8 = 0 at aligned
  have address : (entryAddress base index field).toNat = base + 32 * index + 8 * field.val := by
    rw [entryAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [domain]
  apply BackingLayout.ordinary_mapped
  · rw [address]; omega
  · rw [address]; omega
  · rw [address]; omega

theorem Zone.advance {ι : Type} {objects : ι → TableFamily.Object} {base cap cursor nextCursor : Nat}
    (zone : Zone objects base cap cursor) (forward : cursor ≤ nextCursor) : Zone objects base cap nextCursor :=
  ⟨zone.valid, by have before := zone.earlier; omega, zone.separate⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.Zone.mapped
#print axioms InitECandidate.Solver.GasBudget.Journal.Zone.advance
