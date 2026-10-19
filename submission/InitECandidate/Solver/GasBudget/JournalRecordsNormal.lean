import InitECandidate.Solver.GasBudget.JournalRecordsNormalValues

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
      target.code = source.code ∧ WarmKeys.Environment target ∧ HeapGlobals source target ∧ TableFamily.FloorFrame objects next source target := by
  obtain ⟨paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,codes,nextEnvironment,globals,floorFrame,persistent,nextValues,_pointers⟩ :=
    records_normal_values source target cursor objects base cap count index population entries family image zone countBound inside populations environment (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) (fun _ _ _=>True.intro) deleteCode journal counter normal
  exact ⟨paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,codes,nextEnvironment,globals,floorFrame⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.records_normal
