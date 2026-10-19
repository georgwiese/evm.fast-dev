import InitECandidate.Solver.GasBudget.JournalRecordGeometry
import InitECandidate.Solver.MutableTable.FamilyPersistentFrame
import InitECandidate.Solver.MutableTable.FamilyMetadata

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack PanSemStateFiniteExact MutableTable

/-- A real persistent-word frame preserves the live records and the entire
unused reservation, even when unrelated table arrays relocate. -/
theorem image_zone_framed {ι : Type}
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor nextCursor cutoff base cap count : Nat) (objects next : ι → TableFamily.Object) (entries : Nat → Entry ι)
    (image : Image source objects base count entries) (zone : Zone objects base cap cursor)
    (countBound : count ≤ cap) (forward : cursor ≤ nextCursor) (above : cutoff ≤ base)
    (frame : TableFamily.PersistentFrame cutoff cursor objects next source target) (metadata : TableFamily.Metadata objects next)
    (domain : target.memaddrs = source.memaddrs) : Image target next base count entries ∧ Zone next base cap nextCursor := by
  have entryFrame (index : Nat) (inside : index < cap) (field : Fin 4) :
      TableFamily.Outside next (entryAddress base index field) ∧ target.memory (entryAddress base index field) = source.memory (entryAddress base index field) := by
    have number := entry_number base cap index field zone.valid inside
    have fieldBound := field.isLt
    have before := zone.earlier
    apply frame.words
    · rw [number]; omega
    · rw [number]; omega
    · exact zone.separate index inside field
  have nextZone : Zone next base cap nextCursor :=
    ⟨zone.valid,Nat.le_trans zone.earlier forward,fun index inside field => (entryFrame index inside field).1⟩
  have nextImage : Image target next base count entries := image.transfer domain metadata.pointers metadata.kinds
    (fun index inside field => (entryFrame index (by omega) field).2)
    (fun index inside field => nextZone.separate index (by omega) field)
  exact ⟨nextImage,nextZone⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.image_zone_framed
