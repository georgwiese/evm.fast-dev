import InitECandidate.Solver.GasBudget.RootExitFields

namespace InitECandidate.Solver.GasBudget.RootExit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The exact run_frames root-exit branch, through its actual epilogue and
protected continuation-record loads. It clears go and restores both saved
globals while retaining physical table/journal models and the gas ledger.
Source ownership, arena split and the actual root-kind word remain explicit. -/
theorem selected_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (code : source.code.lookup (ofString "frame_epilogue") = some ([], FrameEpilogue.body, .one))
    (parent previous : BitVec 64) (cut : Nat) (cutSmall : cut < 2 ^ 64)
    (floors : ∀ index, cut ≤ (objects index).floor)
    (contSmall : cont.toNat + 24 ≤ cut) (frameSmall : frame.toNat + 200 ≤ cut)
    (rootMapped : ∀ offset ∈ ([0, 8, 16] : List Nat), source.memaddrs (cont + BitVec.ofNat 64 offset))
    (parentStored : source.memory (cont + 0#64) = .word parent)
    (previousStored : source.memory (cont + 8#64) = .word previous)
    (kindStored : source.memory (cont + 16#64) = .word 0#64)
    (normal : evaluateHOLFiniteState source selected = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      1 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Journal.Image target next base (FrameEpilogue.nextCount err count snap) entries ∧ Journal.Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ FrameEpilogue.price err population count snap + 1 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + FrameEpilogue.removed err count snap) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (FrameEpilogue.nextCount err count snap)))) ∧
      target.locals.lookup (ofString "go") = some (.val (.word 0#64)) ∧
      target.globals.lookup (ofString "ev") = some (.val (.word parent)) ∧
      target.globals.lookup (ofString "cur_cont") = some (.val (.word previous)) ∧ target.code = source.code ∧ WarmKeys.Environment target ∧
      Journal.CounterEffect source target 0 (FrameEpilogue.removed err count snap) 0 ∧ TableFamily.FloorFrame objects next source target ∧ regularBudget target.memory frame = regularBudget source.memory frame := by
  rw [actual_site] at normal
  obtain ⟨skipped, skipRun, restRun⟩ := Input.sequence_none source target .skip _ normal
  have skipActual : evaluateHOLFiniteState source (.skip : ProgHOL 64) = (none, source) := by simp [evaluateHOLFiniteState_skip]
  have skipEq := congrArg Prod.snd (skipRun.symm.trans skipActual)
  change skipped = source at skipEq
  subst skipped
  obtain ⟨calledPost, callRun, choiceRun⟩ := Input.sequence_none source target epilogue (.ite condition rootBranch childBranch) restRun
  obtain ⟨paid, nextCursor, next, positive, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
    locals, codes, nextEnvironment, globals, effect, floorFrame⟩ :=
    FrameEpilogue.call_normal source calledPost cursor objects base cap count snap population entries snapSmall family image zone countBound populations environment
      deleteCode restoreCode journal counter frame cont err ev continuation errorMapped errorStored snapshotMapped snapshotStored code callRun
  have calledCont : calledPost.globals.lookup (ofString "cur_cont") = some (.val (.word cont)) :=
    (globals (ofString "cur_cont") (by decide) (by decide)).trans continuation
  have mapped (offset : Nat) (member : offset ∈ ([0, 8, 16] : List Nat)) : calledPost.memaddrs (cont + BitVec.ofNat 64 offset) := by
    rw [nextEnvironment.domain, ← environment.domain]
    exact rootMapped offset member
  have words (offset : Nat) (inside : offset ≤ 16) : calledPost.memory (cont + BitVec.ofNat 64 offset) = source.memory (cont + BitVec.ofNat 64 offset) :=
    word_below_tables floorFrame cont offset cut floors (by omega) cutSmall
  have kindAfter : calledPost.memory (cont + 16#64) = .word 0#64 := (words 16 (by omega)).trans kindStored
  have kindRead := Input.global_field_read calledPost "cur_cont" cont 16#64 0#64 calledCont (mapped 16 (by simp)) kindAfter
  change eval calledPost (recordLoad 16#64) = some (.val (.word 0#64)) at kindRead
  have test : eval calledPost condition = some (.val (.word 1#64)) := by
    simp only [eval] at kindRead
    simp [eval, condition, evalHOLExact, kindRead, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at test
  rw [evaluateHOLFiniteState_ite, test] at choiceRun
  have rootRun : evaluateHOLFiniteState calledPost rootBranch = (none, target) := by simpa using choiceRun
  have rootEq := root_normal calledPost target cont parent previous calledCont (mapped 0 (by simp))
    ((words 0 (by omega)).trans parentStored) (mapped 8 (by simp)) ((words 8 (by omega)).trans previousStored) rootRun
  subst target
  have fields := root_fields calledPost parent previous
  have rootModels : TableFamily.Model (rootState calledPost parent previous) nextCursor next :=
    models.of_control fields.2.2.2.1 rfl rfl rfl
  have rootImage : Journal.Image (rootState calledPost parent previous) next base (FrameEpilogue.nextCount err count snap) entries :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have rootEffect : Journal.CounterEffect source (rootState calledPost parent previous) 0 (FrameEpilogue.removed err count snap) 0 :=
    effect.trans (Journal.CounterEffect.unchanged calledPost _ fields.2.2.2.2.1)
  have budget := regularBudget_below_tables floorFrame frame cut floors frameSmall cutSmall
  exact ⟨paid, nextCursor, next, positive, fits, clock, forward, rootModels, rootImage, nextZone, bounded, nextPopulations,
    fields.2.2.2.2.1.trans nextCounter, fields.1, fields.2.1, fields.2.2.1, codes, nextEnvironment.of_fields rfl rfl rfl,
    rootEffect, ⟨floorFrame.floors, floorFrame.words⟩, budget⟩

end InitECandidate.Solver.GasBudget.RootExit

#print axioms InitECandidate.Solver.GasBudget.RootExit.selected_normal
