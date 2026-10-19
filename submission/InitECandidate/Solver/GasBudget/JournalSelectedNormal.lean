import InitECandidate.Solver.GasBudget.JournalSelectedNormalValues

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- One actual selected rollback mutation, with a whole-family amortized
price. The branch and its arguments are read from the real journal record. -/
theorem selected_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count index population : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (inside : index < count)
    (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (locals : CallLocals source objects base index (entries index))
    (normal : evaluateHOLFiniteState source selectCall = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base count entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ 38 * population + 39 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + 1) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ HeapGlobals source target ∧ TableFamily.FloorFrame objects next source target := by
  obtain ⟨paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,locals,codes,nextEnvironment,globals,floorFrame,persistent,nextValues⟩ :=
    selected_normal_values source target cursor objects base cap count index population entries family image zone countBound inside populations environment (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) (fun _ _ _=>True.intro) deleteCode locals normal
  exact ⟨paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,locals,codes,nextEnvironment,globals,floorFrame⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.selected_normal
