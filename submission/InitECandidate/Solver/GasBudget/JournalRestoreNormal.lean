import InitECandidate.Solver.GasBudget.JournalRestoreNormalValues

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The complete original state_restore body, including its real zero
return. Current physical ownership is explicit; helper runs, clock funding
and the rollback trace are derived from the actual normal outcome. -/
theorem restore_body_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count snap population : Nat) (entries : Nat → Entry ι) (ordered : snap ≤ count) (small : count < 2 ^ 64)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (snapshot : source.locals.lookup (ofString "snap") = some (.val (.word (BitVec.ofNat 64 snap))))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base snap entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price population (count - snap) + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + (count - snap)) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 snap))) ∧
      target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ TableFamily.FloorFrame objects next source target := by
  obtain ⟨returnedEq,paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,nextCounter,codes,nextEnvironment,globals,floorFrame,persistent,nextValues,nextSaved⟩ :=
    restore_body_normal_values source target cursor objects base cap count snap population entries ordered small family image zone countBound populations environment (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) (fun _ _ _=>True.intro) deleteCode journal counter snapshot returned normal
  exact ⟨returnedEq,paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,nextCounter,codes,nextEnvironment,globals,floorFrame⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.restore_body_normal
