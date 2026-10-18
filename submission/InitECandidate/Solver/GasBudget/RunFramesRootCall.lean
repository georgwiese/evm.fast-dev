import InitECandidate.Solver.GasBudget.RunFramesRootNormal

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The real run_frames caller on a marked root frame, restoring caller
locals after the complete original loop/body return. Its source-clock bound
includes call, loop, epilogue and any actual rollback. Other paths remain open. -/
theorem marked_root_call {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (runCode : source.code.lookup (ofString "run_frames") = some ([], RootExit.runBody, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "run_frames") []) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      3 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Journal.Image target next base (FrameEpilogue.nextCount err count snap) entries ∧ Journal.Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ FrameEpilogue.price err population count snap + 3 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + FrameEpilogue.removed err count snap) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (FrameEpilogue.nextCount err count snap)))) ∧
      target.globals.lookup (ofString "ev") = some (.val (.word parent)) ∧
      target.globals.lookup (ofString "cur_cont") = some (.val (.word previous)) ∧ target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧
      Journal.CounterEffect source target 0 (FrameEpilogue.removed err count snap) 0 ∧ TableFamily.FloorFrame objects next source target ∧ regularBudget target.memory frame = regularBudget source.memory frame := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "run_frames") [] = some (RootExit.runBody, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, runCode]
  obtain ⟨callee, called, calleeLocals⟩ := WitnessRadix.CodeEnvironment.finite_lookup source.code.lookup (ofString "run_frames") [] RootExit.runBody (fun _ => none) .one raw
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "run_frames") [] [] RootExit.runBody callee .one rfl called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryImage : Journal.Image entry objects base count entries :=
    image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  obtain ⟨returnedEq, paid, nextCursor, next, bodyPositive, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
    finalEV, finalCont, codes, nextEnvironment, effect, floorFrame, budget⟩ :=
    marked_root_normal entry post cursor objects base cap count snap population entries snapSmall entryFamily entryImage zone countBound populations
      (environment.of_fields rfl rfl rfl) deleteCode restoreCode journal counter frame cont err ev continuation errorMapped errorStored snapshotMapped snapshotStored code
      parent previous cut cutSmall floors contSmall frameSmall rootMapped parentStored previousStored kindStored flag markedMapped markedStored markedNonzero returned bodyRun
  rw [returnedEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "run_frames") [] [] RootExit.runBody callee .one
    (.val (.word 0#64)) post rfl called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have targetEq := congrArg Prod.snd (normal.symm.trans actual)
  change target = {post with locals := source.locals} at targetEq
  subst target
  change paid ≤ source.clock - 1 at fits
  change post.clock = source.clock - 1 - paid at clock
  refine ⟨1 + paid, nextCursor, next, by omega, by omega, by change post.clock = _; omega, forward,
    models.of_control rfl rfl rfl rfl, ?_, nextZone, by omega, nextPopulations, nextCounter, finalEV, finalCont, rfl, codes,
    nextEnvironment.of_fields rfl rfl rfl, effect, ⟨floorFrame.floors, floorFrame.words⟩, budget⟩
  exact nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.marked_root_call
