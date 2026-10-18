import InitECandidate.Solver.GasBudget.RunFramesRootBody
import InitECandidate.Solver.Input.WhileControlBody

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The real immediately completed root while executes exactly one iteration, then reads
its actual cleared go flag and exits. Funding includes the real loop clock;
all ordinary outcome alternatives, including return/break/continue, are
resolved from execution. Dispatching/child frames are separate obligations. -/
theorem marked_root_loop {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (doneReady : ImmediateDone source frame cont)
    (go : source.locals.lookup (ofString "go") = some (.val (.word 1#64)))
    (result : Option (PanSemResultExact 64)) (control : Input.ControlResult result)
    (normal : evaluateHOLFiniteState source loop = (result, target)) :
    result = none ∧
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      2 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Journal.Image target next base (FrameEpilogue.nextCount err count snap) entries ∧ Journal.Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ FrameEpilogue.price err population count snap + 2 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + FrameEpilogue.removed err count snap) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (FrameEpilogue.nextCount err count snap)))) ∧
      target.locals.lookup (ofString "go") = some (.val (.word 0#64)) ∧
      target.globals.lookup (ofString "ev") = some (.val (.word parent)) ∧
      target.globals.lookup (ofString "cur_cont") = some (.val (.word previous)) ∧ target.code = source.code ∧ WarmKeys.Environment target ∧
      Journal.CounterEffect source target 0 (FrameEpilogue.removed err count snap) 0 ∧ TableFamily.FloorFrame objects next source target ∧ regularBudget target.memory frame = regularBudget source.memory frame := by
  have test : eval source condition = some (.val (.word 1#64)) := by
    simp [eval, condition, evalHOLExact, localVar, toExact, go, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨positive, middle, bodyResult, bodyRun, bodyControl, clockBound⟩ :=
    Input.while_control_body source target condition loopBody test result control normal
  let entry := decClockHOLFinite source
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryImage : Journal.Image entry objects base count entries :=
    image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  obtain ⟨bodyNone, paid, nextCursor, next, bodyPositive, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
    nextGo, finalEV, finalCont, codes, nextEnvironment, effect, floorFrame, budget⟩ :=
    marked_root_body entry middle cursor objects base cap count snap population entries snapSmall entryFamily entryImage zone countBound populations
      (environment.of_fields rfl rfl rfl) deleteCode restoreCode journal counter frame cont err ev continuation errorMapped errorStored snapshotMapped snapshotStored code
      parent previous cut cutSmall floors contSmall frameSmall rootMapped parentStored previousStored kindStored (doneReady.of_fields rfl rfl) bodyResult bodyControl bodyRun
  rw [bodyNone] at bodyRun
  have tailRun := normal
  rw [loop, evaluateHOLFiniteState_while_total] at tailRun
  simp only [eval, evalHOLFinite] at test tailRun
  rw [test] at tailRun
  simp only [if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide), if_neg (show source.clock ≠ 0 from by omega)] at tailRun
  rw [bodyRun, WitnessRadix.StateSteps.fixed_clock entry middle none clockBound] at tailRun
  have doneTest : eval middle condition = some (.val (.word 0#64)) := by
    simp [eval, condition, evalHOLExact, localVar, toExact, nextGo, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have finished : evaluateHOLFiniteState middle loop = (none, middle) := by
    rw [loop, evaluateHOLFiniteState_while_total]
    simp only [eval, evalHOLFinite] at doneTest ⊢
    rw [doneTest]
    simp
  have same := tailRun.symm.trans finished
  have resultEq := congrArg Prod.fst same
  have targetEq := congrArg Prod.snd same
  change target = middle at targetEq
  subst target
  change paid ≤ source.clock - 1 at fits
  change middle.clock = source.clock - 1 - paid at clock
  exact ⟨resultEq, 1 + paid, nextCursor, next, by omega, by omega, by omega, forward, models, nextImage, nextZone,
    by omega, nextPopulations, nextCounter, nextGo, finalEV, finalCont, codes, nextEnvironment, effect,
    ⟨floorFrame.floors, floorFrame.words⟩, budget⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.marked_root_loop
