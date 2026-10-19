import InitECandidate.Solver.GasBudget.JournalLoopValues

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Whole original rollback loop. The actual unsigned journal counter derives
the iteration count. Every iteration retains all remaining physical records
and live tables; growth potential telescopes across different writers. -/
theorem loop_normal {ι : Type} [Fintype ι] [DecidableEq ι] (remaining : Nat)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count snap population : Nat) (entries : Nat → Entry ι)
    (countEq : count = snap + remaining) (small : count < 2 ^ 64)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (snapshot : source.locals.lookup (ofString "snap") = some (.val (.word (BitVec.ofNat 64 snap))))
    (normal : evaluateHOLFiniteState source loop = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base snap entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price population remaining + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + remaining) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 snap))) ∧
      target.locals.lookup (ofString "snap") = some (.val (.word (BitVec.ofNat 64 snap))) ∧
      target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ TableFamily.FloorFrame objects next source target := by
  obtain ⟨paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,nextCounter,nextSnapshot,codes,nextEnvironment,globals,floorFrame,persistent,nextValues,nextSaved,_pointers⟩ :=
    loop_normal_values remaining source target cursor objects base cap count snap population entries countEq small family image zone countBound populations environment (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) (fun _ _ _=>True.intro) deleteCode journal counter snapshot normal
  exact ⟨paid,nextCursor,next,fits,clock,forward,models,nextImage,nextZone,bounded,populationsAfter,nextCounter,nextSnapshot,codes,nextEnvironment,globals,floorFrame⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.price_step
#print axioms InitECandidate.Solver.GasBudget.Journal.loop_normal
