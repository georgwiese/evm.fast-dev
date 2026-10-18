import InitECandidate.Solver.GasBudget.FrameEpilogueChoice
import InitECandidate.Solver.MutableTable.FamilyControl

namespace InitECandidate.Solver.GasBudget.FrameEpilogue
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Complete actual epilogue body, retaining physical journal/table ownership
and the exact counter decrease through its real zero return. -/
theorem body_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count snap population : Nat) (entries : Nat → Journal.Entry ι) (snapSmall : snap < 2 ^ 64)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (populations : ∀ table, (objects table).slots.length ≤ population) (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (restoreCode : source.code.lookup (ofString "state_restore") = some (Journal.formals, Journal.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (frame cont err : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (continuation : source.globals.lookup (ofString "cur_cont") = some (.val (.word cont)))
    (errorMapped : source.memaddrs (frame + 160#64)) (errorStored : source.memory (frame + 160#64) = .word err)
    (snapshotMapped : source.memaddrs (cont + 24#64)) (snapshotStored : source.memory (cont + 24#64) = .word (BitVec.ofNat 64 snap))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Journal.Image target next base (nextCount err count snap) entries ∧ Journal.Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price err population count snap + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + removed err count snap) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (nextCount err count snap)))) ∧
      target.code = source.code ∧ WarmKeys.Environment target ∧ Journal.OtherGlobals source target := by
  rw [body_shape] at normal
  obtain ⟨middle, choiceRun, returnRun, saved⟩ := choice_safe.normal_continue source target (.return (.const 0#64)) returned normal
  obtain ⟨paid, nextCursor, next, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
    locals, codes, nextEnvironment, globals⟩ :=
    choice_normal source middle cursor objects base cap count snap population entries snapSmall family image zone countBound populations environment
      deleteCode restoreCode journal counter frame cont err ev continuation errorMapped errorStored snapshotMapped snapshotStored choiceRun
  have actualReturn : evaluateHOLFiniteState middle (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite middle) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have returnedEq : returned = .val (.word 0#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst (returnRun.symm.trans actualReturn)
  have same := congrArg Prod.snd (returnRun.symm.trans actualReturn)
  change target = emptyLocalsHOLFinite middle at same
  subst target
  refine ⟨returnedEq, paid, nextCursor, next, fits, clock, forward, models.of_control rfl rfl rfl rfl,
    ?_, nextZone, bounded, nextPopulations, nextCounter, codes, nextEnvironment.of_fields rfl rfl rfl, globals⟩
  exact nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate

end InitECandidate.Solver.GasBudget.FrameEpilogue

#print axioms InitECandidate.Solver.GasBudget.FrameEpilogue.body_normal
