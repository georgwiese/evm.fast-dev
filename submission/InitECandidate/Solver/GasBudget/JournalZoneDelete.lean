import InitECandidate.Solver.GasBudget.JournalZone
import InitECandidate.Solver.MutableTable.FamilyDelete

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- An actual original deletion with any mapped query retains the complete
journal reservation and its live image. Table plans and heap stay fixed. -/
theorem delete_zone_normal {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι) (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (environment : WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word (objects writer).pointer), .val (.word query)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_del") arguments) = (none, target)) :
    ∃ (paid : Nat) (next : TableFamily.Object), paid ≤ Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1 ∧
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
      TableFamily.Model target cursor (Function.update objects writer next) ∧
      Image target (Function.update objects writer next) base count entries ∧ Zone (Function.update objects writer next) base cap cursor ∧
      next.slots.length ≤ (objects writer).slots.length ∧ target.locals = source.locals ∧ target.globals = source.globals ∧
      target.code = source.code ∧ WarmKeys.Environment target := by
  obtain ⟨paid, next, bounded, fits, clock, kind, plan, floor, models, pointers, lower, upper, locals, globals, codes, nextEnvironment, protectedWords⟩ :=
    TableFamily.delete_normal source target cursor objects writer family environment query queryFits queryMapped deleteCode arguments args normal
  have kinds (table : ι) : (Function.update objects writer next table).kind = (objects table).kind := by
    by_cases same : table = writer
    · subst table; simpa only [Function.update_self] using kind
    · rw [Function.update_of_ne same]
  have plans (table : ι) : (Function.update objects writer next table).plan = (objects table).plan := by
    by_cases same : table = writer
    · subst table; simpa only [Function.update_self] using plan
    · rw [Function.update_of_ne same]
  have nextZone : Zone (Function.update objects writer next) base cap cursor := by
    refine ⟨zone.valid, zone.earlier, ?_⟩
    intro index inside field table
    rw [kinds, plans]
    exact zone.separate index inside field table
  have nextImage : Image target (Function.update objects writer next) base count entries :=
    image.transfer (nextEnvironment.domain.trans environment.domain.symm) pointers kinds
      (fun index inside field => protectedWords _ (image.separate index inside field writer))
      (fun index inside field table => by rw [kinds, plans]; exact image.separate index inside field table)
  exact ⟨paid, next, bounded, fits, clock, kind, plan, models, nextImage, nextZone, upper, locals, globals, codes, nextEnvironment⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.delete_zone_normal
