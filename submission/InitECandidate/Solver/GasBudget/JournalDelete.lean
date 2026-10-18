import InitECandidate.Solver.GasBudget.JournalImage
import InitECandidate.Solver.MutableTable.FamilyDelete

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Actual rollback deletion retains all unread records, query mappings and
live tables, including tables preceding the fixed journal allocation. -/
theorem delete_image_normal {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (objects : ι → TableFamily.Object) (base count index : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries) (inside : index < count)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (MutableTable.Find.formals, MutableTable.Delete.body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word (objects (entries index).writer).pointer), .val (.word (entries index).key)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_del") arguments) = (none, target)) :
    ∃ (paid : Nat) (next : TableFamily.Object),
      paid ≤ Delete.modelPrice (objects (entries index).writer).kind (objects (entries index).writer).slots.length + 1 ∧
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      next.kind = (objects (entries index).writer).kind ∧ next.plan = (objects (entries index).writer).plan ∧
      TableFamily.Model target cursor (Function.update objects (entries index).writer next) ∧
      Image target (Function.update objects (entries index).writer next) base count entries ∧
      next.slots.length ≤ (objects (entries index).writer).slots.length ∧
      target.locals = source.locals ∧ target.globals = source.globals ∧ target.code = source.code ∧ WarmKeys.Environment target := by
  let writer := (entries index).writer
  obtain ⟨paid, next, bounded, fits, clock, kind, plan, floor, models, pointers, lower, upper, locals, globals, codes, nextEnvironment, protectedWords⟩ :=
    TableFamily.delete_normal source target cursor objects writer family environment (entries index).key
      (image.queryFits index inside) (image.queryMapped index inside) deleteCode arguments args normal
  have kinds (table : ι) : (Function.update objects writer next table).kind = (objects table).kind := by
    by_cases same : table = writer
    · subst table; simpa only [Function.update_self] using kind
    · rw [Function.update_of_ne same]
  have plans (table : ι) : (Function.update objects writer next table).plan = (objects table).plan := by
    by_cases same : table = writer
    · subst table; simpa only [Function.update_self] using plan
    · rw [Function.update_of_ne same]
  have nextImage : Image target (Function.update objects writer next) base count entries := by
    apply image.transfer (nextEnvironment.domain.trans environment.domain.symm) pointers kinds
    · intro i bounded field
      exact protectedWords _ (image.separate i bounded field writer)
    · intro i bounded field table
      rw [kinds, plans]
      exact image.separate i bounded field table
  exact ⟨paid, next, bounded, fits, clock, kind, plan, models, nextImage, upper, locals, globals, codes, nextEnvironment⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.delete_image_normal
