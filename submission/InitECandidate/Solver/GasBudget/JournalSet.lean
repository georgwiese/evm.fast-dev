import InitECandidate.Solver.GasBudget.JournalImage
import InitECandidate.Solver.MutableTable.FamilySet

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The actual rollback reinsertion preserves the entire journal image,
including records adjacent to old table pools and every copied key mapping.
Growth is charged by the writer's potential increase. -/
theorem set_image_normal {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (objects : ι → TableFamily.Object) (base count index : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (extent : base + 32 * count ≤ cursor) (inside : index < count)
    (environment : WarmKeys.Environment source) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (MutableTable.TableCall.values (objects (entries index).writer).pointer (entries index).key (entries index).value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      next.kind = (objects (entries index).writer).kind ∧
      TableFamily.Model target nextCursor (Function.update objects (entries index).writer next) ∧
      Image target (Function.update objects (entries index).writer next) base count entries ∧
      paid + GrowRuntime.growthPotential (objects (entries index).writer).kind (objects (entries index).writer).plan.capacity ≤
        Set.noGrowthPrice (objects (entries index).writer).kind (objects (entries index).writer).slots.length + 1 +
          GrowRuntime.growthPotential (objects (entries index).writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects (entries index).writer).slots.length + 1 ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ HeapGlobals source target := by
  let writer := (entries index).writer
  obtain ⟨paid, nextCursor, next, fits, clock, forward, kind, floor, models, pointers, amortized, lower, upper, capacity,
      locals, codes, nextEnvironment, globals, beforeFloor, earlier⟩ :=
    TableFamily.set_normal source target cursor objects writer family environment (entries index).key (entries index).value arguments
      (image.queryFits index inside) (image.queryMapped index inside) args normal
  have cursorSmall : cursor < 2 ^ 64 := by have bounded := (family.tables writer).bounded; omega
  have words (i : Nat) (bounded : i < count) (field : Fin 4) :=
    earlier (entryAddress base i field) (entry_before base count cursor i field extent cursorSmall bounded) (image.separate i bounded field writer)
  have kinds (table : ι) : (Function.update objects writer next table).kind = (objects table).kind := by
    by_cases same : table = writer
    · subst table; simpa only [Function.update_self] using kind
    · rw [Function.update_of_ne same]
  have nextImage : Image target (Function.update objects writer next) base count entries := by
    apply image.transfer (nextEnvironment.domain.trans environment.domain.symm) pointers kinds
    · intro i bounded field
      exact (words i bounded field).2
    · intro i bounded field table
      by_cases same : table = writer
      · subst table
        simpa only [Function.update_self] using (words i bounded field).1
      · simpa only [Function.update_of_ne same] using image.separate i bounded field table
  exact ⟨paid, nextCursor, next, fits, clock, forward, kind, models, nextImage, amortized, upper, locals, codes, nextEnvironment, globals⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.set_image_normal
