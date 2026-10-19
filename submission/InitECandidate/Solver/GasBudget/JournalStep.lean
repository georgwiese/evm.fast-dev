import InitECandidate.Solver.GasBudget.JournalStepValues

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- One complete actual original rollback body. The executed decrement and
record loads choose the writer; the helper preserves the new counter and all
remaining record images. No helper execution or iteration budget is assumed. -/
theorem body_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count population : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (positive : 0 < count)
    (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (normal : evaluateHOLFiniteState source loopBody = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base (count - 1) entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ 38 * population + 39 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + 1) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count - 1)))) ∧
      target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ TableFamily.FloorFrame objects next source target := by
  obtain ⟨paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,nextCounter,codes,nextEnvironment,globals,floorFrame,persistent,nextValues,nextSaved⟩ :=
    body_normal_values source target cursor objects base cap count population entries family image zone countBound positive populations environment (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) (fun _ _ _=>True.intro) deleteCode journal counter normal
  exact ⟨paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,nextCounter,codes,nextEnvironment,globals,floorFrame⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.OtherGlobals.trans
#print axioms InitECandidate.Solver.GasBudget.Journal.body_normal
