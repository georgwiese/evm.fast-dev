import InitECandidate.Solver.GasBudget.RunFramesMarked
import InitECandidate.Solver.GasBudget.RootExitControl
import InitECandidate.Solver.Input.ScopeLookup

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The complete marked-root loop body, including done's real lexical scope.
An ordinary control outcome is proved to be normal, not a hidden break or
continue, and its actual go flag is zero with all resource models retained. -/
theorem marked_root_body {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (flag : BitVec 64) (markedMapped : source.memaddrs (cont + 32#64))
    (markedStored : source.memory (cont + 32#64) = .word flag) (markedNonzero : flag ≠ 0#64)
    (result : Option (PanSemResultExact 64)) (control : Input.ControlResult result)
    (normal : evaluateHOLFiniteState source loopBody = (result, target)) :
    result = none ∧
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
  have actual := marked_body_execute source cont flag continuation markedMapped markedStored markedNonzero
  rw [actual] at normal
  let entered := markedState source
  let inner := (evaluateHOLFiniteState entered RootExit.selected).2
  have firstResult := congrArg Prod.fst normal
  change (evaluateHOLFiniteState entered RootExit.selected).1 = result at firstResult
  have resultRun : evaluateHOLFiniteState entered RootExit.selected = (result, inner) := Prod.ext firstResult rfl
  have targetEq := congrArg Prod.snd normal
  change restore source "done" inner = target at targetEq
  have entryFamily : TableFamily.Model entered cursor objects := family.of_control rfl rfl rfl rfl
  have entryImage : Journal.Image entered objects base count entries :=
    image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have entryEnvironment : WarmKeys.Environment entered := environment.of_fields rfl rfl rfl
  have resultEq := RootExit.selected_control entered inner cursor objects base cap count snap population entries snapSmall entryFamily entryImage zone countBound populations entryEnvironment
    deleteCode restoreCode journal counter frame cont err ev continuation errorMapped errorStored snapshotMapped snapshotStored code cut cutSmall floors contSmall
    (rootMapped 16 (by simp)) kindStored result control resultRun
  rw [resultEq] at resultRun
  obtain ⟨paid, nextCursor, next, positive, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
    go, finalEV, finalCont, codes, nextEnvironment, effect, floorFrame, budget⟩ :=
    RootExit.selected_normal entered inner cursor objects base cap count snap population entries snapSmall entryFamily entryImage zone countBound populations entryEnvironment
      deleteCode restoreCode journal counter frame cont err ev continuation errorMapped errorStored snapshotMapped snapshotStored code parent previous cut cutSmall floors contSmall frameSmall
      rootMapped parentStored previousStored kindStored resultRun
  subst target
  have finalGo : (restore source "done" inner).locals.lookup (ofString "go") = some (.val (.word 0#64)) :=
    (Input.ScalarScope.restore_other source inner "done" "go" (by decide)).trans go
  refine ⟨resultEq, paid, nextCursor, next, positive, fits, clock, forward, models.of_control rfl rfl rfl rfl,
    ?_, nextZone, bounded, nextPopulations, nextCounter, finalGo, finalEV, finalCont, codes,
    nextEnvironment.of_fields rfl rfl rfl, effect, ⟨floorFrame.floors, floorFrame.words⟩, budget⟩
  exact nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.marked_root_body
