import InitECandidate.Solver.GasBudget.FrameEpilogueNormal

namespace InitECandidate.Solver.GasBudget.FrameEpilogue
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The actual run_frames epilogue caller preserves its caller locals and
accounts for exactly the journal records removed by the real error branch. -/
theorem call_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (code : source.code.lookup (ofString "frame_epilogue") = some ([], body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "frame_epilogue") []) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      1 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Journal.Image target next base (nextCount err count snap) entries ∧ Journal.Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price err population count snap + 1 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + removed err count snap) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (nextCount err count snap)))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ Journal.OtherGlobals source target ∧
      Journal.CounterEffect source target 0 (removed err count snap) 0 := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "frame_epilogue") [] = some (body, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, calleeLocals⟩ := WitnessRadix.CodeEnvironment.finite_lookup source.code.lookup (ofString "frame_epilogue") [] body (fun _ => none) .one raw
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "frame_epilogue") [] [] body callee .one rfl called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryImage : Journal.Image entry objects base count entries :=
    image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  obtain ⟨returnedEq, paid, nextCursor, next, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
    codes, nextEnvironment, globals, effect⟩ :=
    body_normal entry post cursor objects base cap count snap population entries snapSmall entryFamily entryImage zone countBound populations
      (environment.of_fields rfl rfl rfl) deleteCode restoreCode journal counter frame cont err ev continuation errorMapped errorStored snapshotMapped snapshotStored returned bodyRun
  rw [returnedEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "frame_epilogue") [] [] body callee .one
    (.val (.word 0#64)) post rfl called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have targetEq := congrArg Prod.snd (normal.symm.trans actual)
  change target = {post with locals := source.locals} at targetEq
  subst target
  change paid ≤ source.clock - 1 at fits
  change post.clock = source.clock - 1 - paid at clock
  refine ⟨1 + paid, nextCursor, next, by omega, by omega, by change post.clock = _; omega, forward,
    models.of_control rfl rfl rfl rfl, ?_, nextZone, by omega, nextPopulations, nextCounter, rfl, codes,
    nextEnvironment.of_fields rfl rfl rfl, globals, effect⟩
  exact nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate

end InitECandidate.Solver.GasBudget.FrameEpilogue

#print axioms InitECandidate.Solver.GasBudget.FrameEpilogue.call_normal
