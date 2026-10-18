import InitECandidate.Solver.GasBudget.JournalZone
import InitECandidate.Solver.MutableTable.FamilySet

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- An arbitrary actual setter retains the entire journal reservation,
including unused slots, as well as its live prefix image. This applies to
the final append mutation with the original query rather than its copy. -/
theorem set_zone_normal {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι) (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (query value : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (TableCall.values (objects writer).pointer query value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = (objects writer).kind ∧
      TableFamily.Model target nextCursor (Function.update objects writer next) ∧
      Image target (Function.update objects writer next) base count entries ∧ Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Set.noGrowthPrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧ target.locals = source.locals ∧ target.code = source.code ∧
      WarmKeys.Environment target ∧ HeapGlobals source target := by
  obtain ⟨paid, nextCursor, next, fits, clock, forward, kind, floor, models, pointers, bounded, lower, upper, capacity, locals, codes, nextEnvironment, globals, beforeFloor, earlier⟩ :=
    TableFamily.set_normal source target cursor objects writer family environment query value arguments queryFits queryMapped args normal
  have cursorSmall : cursor < 2 ^ 64 := by have bounded := (family.tables writer).bounded; omega
  have words (index : Nat) (inside : index < cap) (field : Fin 4) :=
    earlier (entryAddress base index field) (entry_before base cap cursor index field zone.earlier cursorSmall inside) (zone.separate index inside field writer)
  have kinds (table : ι) : (Function.update objects writer next table).kind = (objects table).kind := by
    by_cases same : table = writer
    · subst table; simpa only [Function.update_self] using kind
    · rw [Function.update_of_ne same]
  have nextZone : Zone (Function.update objects writer next) base cap nextCursor := by
    refine ⟨zone.valid, by have before := zone.earlier; omega, ?_⟩
    intro index inside field table
    by_cases same : table = writer
    · subst table; simpa only [Function.update_self] using (words index inside field).1
    · simpa only [Function.update_of_ne same] using zone.separate index inside field table
  have nextImage : Image target (Function.update objects writer next) base count entries :=
    image.transfer (nextEnvironment.domain.trans environment.domain.symm) pointers kinds
      (fun index inside field => (words index (by omega) field).2)
      (fun index inside field => nextZone.separate index (by omega) field)
  exact ⟨paid, nextCursor, next, fits, clock, forward, kind, models, nextImage, nextZone, bounded, upper, locals, codes, nextEnvironment, globals⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.set_zone_normal
