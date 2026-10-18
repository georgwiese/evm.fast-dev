import InitECandidate.Solver.GasBudget.JournalSelectedNormal

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The actual scoped record loads, branch and mutation compose with no
intermediate helper execution or source-clock budget premise. -/
theorem records_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count index population : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (inside : index < count)
    (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 index))))
    (normal : evaluateHOLFiniteState source records = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base count entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ 38 * population + 39 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + 1) ∧
      target.code = source.code ∧ WarmKeys.Environment target ∧ HeapGlobals source target := by
  have actual := records_execute source objects base count index entries inside image journal counter
  rw [actual] at normal
  let entry := entered source objects base index (entries index)
  let called := (evaluateHOLFiniteState entry selectCall).2
  have result := congrArg Prod.fst normal
  change (evaluateHOLFiniteState entry selectCall).1 = none at result
  have selected : evaluateHOLFiniteState entry selectCall = (none, called) := Prod.ext result rfl
  have targetEq := congrArg Prod.snd normal
  change restored source called = target at targetEq
  have entryFamily : TableFamily.Model entry cursor objects :=
    ⟨fun table => (family.tables table).of_fields rfl rfl rfl rfl, family.apart⟩
  have entryImage : Image entry objects base count entries :=
    image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have entryEnvironment : WarmKeys.Environment entry := environment.of_fields rfl rfl rfl
  obtain ⟨paid, nextCursor, next, fits, clock, forward, nextFamily, nextImage, nextZone, bounded, nextPopulations, localEq, codes, nextEnvironment, globals⟩ :=
    selected_normal entry called cursor objects base cap count index population entries entryFamily entryImage zone countBound inside populations entryEnvironment deleteCode
      (CallLocals.entered source objects base index (entries index)) selected
  subst target
  have finalFamily : TableFamily.Model (restored source called) nextCursor next :=
    ⟨fun table => (nextFamily.tables table).of_fields rfl rfl rfl rfl, nextFamily.apart⟩
  have finalImage : Image (restored source called) next base count entries :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  exact ⟨paid, nextCursor, next, fits, clock, forward, finalFamily, finalImage, nextZone, bounded, nextPopulations, codes,
    nextEnvironment.of_fields rfl rfl rfl, globals⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.records_normal
