import InitECandidate.Solver.GasBudget.FrameEpilogueProgram

namespace InitECandidate.Solver.GasBudget.FrameEpilogue
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Both actual epilogue branches: success does no rollback, and an error
removes exactly count-min(count,snapshot) live records. Each reached restore
supplies its own allocation room and call clocks. -/
theorem choice_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (normal : evaluateHOLFiniteState source choice = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Journal.Image target next base (nextCount err count snap) entries ∧ Journal.Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price err population count snap + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + removed err count snap) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (nextCount err count snap)))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ Journal.OtherGlobals source target := by
  have test := condition_read source frame err ev errorMapped errorStored
  simp only [eval] at test
  rw [choice, evaluateHOLFiniteState_ite, test] at normal
  by_cases zero : err = 0#64
  · have same : target = source := by
      have actual : evaluateHOLFiniteState source (.skip : ProgHOL 64) = (none, source) := by simp [evaluateHOLFiniteState_skip]
      have selected : evaluateHOLFiniteState source (.skip : ProgHOL 64) = (none, target) := by simpa [zero] using normal
      exact congrArg Prod.snd (selected.symm.trans actual)
    subst target
    refine ⟨0, cursor, objects, Nat.zero_le _, by simp, Nat.le_refl _, family, ?_, zone, ?_, ?_, ?_, rfl, rfl, environment, Journal.OtherGlobals.refl source⟩
    · simpa only [nextCount, if_pos zero] using image
    · simp [price, zero]
    · simpa only [removed, if_pos zero, Nat.add_zero] using populations
    · simpa only [nextCount, if_pos zero] using counter
  · have restoreRun : evaluateHOLFiniteState source rollback = (none, target) := by simpa [zero] using normal
    have snapshotRead := Input.global_field_read source "cur_cont" cont 24#64 (BitVec.ofNat 64 snap) continuation snapshotMapped snapshotStored
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [snapshot] =
        some [.val (.word (BitVec.ofNat 64 snap))] := by
      simp only [eval] at snapshotRead
      simp [evalListHOLFinite, evalListHOLExact, snapshot, snapshotRead]
    have countSmall : count < 2 ^ 64 := by
      have upper := zone.valid.upper
      change base + 32 * cap ≤ 33806089496 at upper
      omega
    obtain ⟨paid, nextCursor, next, positive, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
      locals, codes, nextEnvironment, globals⟩ :=
      Journal.restore_call_bound source target cursor objects base cap count snap population entries countSmall snapSmall family image zone countBound populations environment
        deleteCode restoreCode journal counter [snapshot] args restoreRun
    exact ⟨paid, nextCursor, next, fits, clock, forward, models, by simpa only [nextCount, if_neg zero] using nextImage, nextZone,
      by simpa only [price, if_neg zero] using bounded,
      by simpa only [removed, if_neg zero] using nextPopulations,
      by simpa only [nextCount, if_neg zero] using nextCounter, locals, codes, nextEnvironment, globals⟩

end InitECandidate.Solver.GasBudget.FrameEpilogue

#print axioms InitECandidate.Solver.GasBudget.FrameEpilogue.choice_normal
