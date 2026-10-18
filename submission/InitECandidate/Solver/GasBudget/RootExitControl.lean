import InitECandidate.Solver.GasBudget.RootExitNormal
import InitECandidate.Solver.Input.ControlContinue

namespace InitECandidate.Solver.GasBudget.RootExit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- A reachable root exit cannot hide an outer return, break or continue.
Actual control outcomes force its epilogue call and root assignment branch
normal before the enclosing while is inverted. -/
theorem selected_control {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (cut : Nat) (cutSmall : cut < 2 ^ 64)
    (floors : ∀ index, cut ≤ (objects index).floor)
    (contSmall : cont.toNat + 24 ≤ cut)
    (kindMapped : source.memaddrs (cont + 16#64))
    (kindStored : source.memory (cont + 16#64) = .word 0#64)
    (result : Option (PanSemResultExact 64)) (control : Input.ControlResult result)
    (run : evaluateHOLFiniteState source selected = (result, target)) : result = none := by
  rw [actual_site] at run
  obtain ⟨skipped, skipRun, restRun, skipSaved⟩ := Input.LocalPrefix.skip.control_continue (key := ofString "setup") source target _ result control run
  have skipActual : evaluateHOLFiniteState source (.skip : ProgHOL 64) = (none, source) := by simp [evaluateHOLFiniteState_skip]
  have skipEq := congrArg Prod.snd (skipRun.symm.trans skipActual)
  change skipped = source at skipEq
  subst skipped
  have epilogueSafe : Input.LocalPrefix (ofString "setup") epilogue := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨calledPost, callRun, choiceRun, callSaved⟩ := epilogueSafe.control_continue source target (.ite condition rootBranch childBranch) result control restRun
  obtain ⟨paid, nextCursor, next, positive, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
    locals, codes, nextEnvironment, globals, effect, floorFrame⟩ :=
    FrameEpilogue.call_normal source calledPost cursor objects base cap count snap population entries snapSmall family image zone countBound populations environment
      deleteCode restoreCode journal counter frame cont err ev continuation errorMapped errorStored snapshotMapped snapshotStored code callRun
  have calledCont : calledPost.globals.lookup (ofString "cur_cont") = some (.val (.word cont)) :=
    (globals (ofString "cur_cont") (by decide) (by decide)).trans continuation
  have mapped : calledPost.memaddrs (cont + 16#64) := by
    rw [nextEnvironment.domain, ← environment.domain]
    exact kindMapped
  have kindAfter : calledPost.memory (cont + 16#64) = .word 0#64 :=
    (word_below_tables floorFrame cont 16 cut floors (by omega) cutSmall).trans kindStored
  have kindRead := Input.global_field_read calledPost "cur_cont" cont 16#64 0#64 calledCont mapped kindAfter
  change eval calledPost (recordLoad 16#64) = some (.val (.word 0#64)) at kindRead
  have test : eval calledPost condition = some (.val (.word 1#64)) := by
    simp only [eval] at kindRead
    simp [eval, condition, evalHOLExact, kindRead, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at test
  rw [evaluateHOLFiniteState_ite, test] at choiceRun
  have rootRun : evaluateHOLFiniteState calledPost rootBranch = (result, target) := by simpa using choiceRun
  have safe : Input.LocalPrefix (ofString "setup") rootBranch :=
    .seq (.globalAssign _ _) (.seq (.globalAssign _ _) (.assign _ _ (by decide)))
  exact safe.control_none calledPost target result control rootRun

end InitECandidate.Solver.GasBudget.RootExit

#print axioms InitECandidate.Solver.GasBudget.RootExit.selected_control
