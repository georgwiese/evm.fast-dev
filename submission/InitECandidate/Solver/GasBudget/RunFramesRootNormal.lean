import InitECandidate.Solver.GasBudget.RunFramesRootLoop
import InitECandidate.Solver.Input.SequenceControl
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Complete original run_frames body on an already-marked root frame,
including the actual go declaration, sole iteration, real final return and
both lexical restorations. Other dispatch/child paths are still open. -/
theorem marked_root_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source RootExit.runBody = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      2 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Journal.Image target next base (FrameEpilogue.nextCount err count snap) entries ∧ Journal.Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ FrameEpilogue.price err population count snap + 2 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + FrameEpilogue.removed err count snap) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (FrameEpilogue.nextCount err count snap)))) ∧
      target.globals.lookup (ofString "ev") = some (.val (.word parent)) ∧
      target.globals.lookup (ofString "cur_cont") = some (.val (.word previous)) ∧ target.code = source.code ∧ WarmKeys.Environment target ∧
      Journal.CounterEffect source target 0 (FrameEpilogue.removed err count snap) 0 ∧ TableFamily.FloorFrame objects next source target ∧ regularBudget target.memory frame = regularBudget source.memory frame := by
  rw [body_shape] at normal
  obtain ⟨declared, inner, read, shape, sequenceRun, restored⟩ := Input.CallNormal.declaration_normal_entry source target "go" .one (.const 1#64)
    (.seq loop (.return (.const 0#64))) returned normal
  have declaredEq : declared = .val (.word 1#64) := by
    simpa only [eval, evalHOLExact, Option.some.injEq] using read.symm
  subst declared
  let entry := bind source "go" 1#64
  obtain ⟨loopPost, loopResult, loopRun, loopControl, tailIf⟩ := Input.sequence_control_first entry inner loop (.return (.const 0#64))
    (some (.returned returned)) (.returned returned) sequenceRun
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryImage : Journal.Image entry objects base count entries :=
    image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  obtain ⟨loopNone, paid, nextCursor, next, positive, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
    nextGo, finalEV, finalCont, codes, nextEnvironment, effect, floorFrame, budget⟩ :=
    marked_root_loop entry loopPost cursor objects base cap count snap population entries snapSmall entryFamily entryImage zone countBound populations
      (environment.of_fields rfl rfl rfl) deleteCode restoreCode journal counter frame cont err ev continuation errorMapped errorStored snapshotMapped snapshotStored code
      parent previous cut cutSmall floors contSmall frameSmall rootMapped parentStored previousStored kindStored flag markedMapped markedStored markedNonzero
      (bind_lookup_same _ _ _) loopResult loopControl loopRun
  have tailRun := tailIf loopNone
  have actualReturn : evaluateHOLFiniteState loopPost (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite loopPost) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have returnedEq : returned = .val (.word 0#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst (tailRun.symm.trans actualReturn)
  have innerEq := congrArg Prod.snd (tailRun.symm.trans actualReturn)
  change inner = emptyLocalsHOLFinite loopPost at innerEq
  have targetEq : target = restore source "go" (emptyLocalsHOLFinite loopPost) := restored.trans (congrArg (restore source "go") innerEq)
  rw [targetEq]
  refine ⟨returnedEq, paid, nextCursor, next, positive, fits, clock, forward, models.of_control rfl rfl rfl rfl,
    ?_, nextZone, bounded, nextPopulations, nextCounter, finalEV, finalCont, codes, nextEnvironment.of_fields rfl rfl rfl,
    effect, ⟨floorFrame.floors, floorFrame.words⟩, budget⟩
  exact nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.marked_root_normal
