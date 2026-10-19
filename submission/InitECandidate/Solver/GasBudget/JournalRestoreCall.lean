import InitECandidate.Solver.GasBudget.JournalRestoreCallValues

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Actual original state_restore caller. The real journal counter supplies
the iteration count; the actual normal call supplies all clock funding. -/
theorem restore_call_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count snap population : Nat) (entries : Nat → Entry ι) (ordered : snap ≤ count) (small : count < 2 ^ 64)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (code : source.code.lookup (ofString "state_restore") = some (formals, body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (BitVec.ofNat 64 snap))])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "state_restore") arguments) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      1 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base snap entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price population (count - snap) + 1 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + (count - snap)) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 snap))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ TableFamily.FloorFrame objects next source target := by
  obtain ⟨paid,nextCursor,next,positive,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,nextCounter,locals,codes,nextEnvironment,globals,floorFrame,persistent,nextValues,nextSaved⟩ :=
    restore_call_normal_values source target cursor objects base cap count snap population entries ordered small family image zone countBound populations environment (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) (fun _ _ _=>True.intro) deleteCode code journal counter arguments args normal
  exact ⟨paid,nextCursor,next,positive,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,nextCounter,locals,codes,nextEnvironment,globals,floorFrame⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.restore_call_normal
