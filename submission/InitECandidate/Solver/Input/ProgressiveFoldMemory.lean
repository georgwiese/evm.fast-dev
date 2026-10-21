import InitECandidate.Solver.Input.ProgressiveSuffixCost
import InitECandidate.Solver.Input.ShaPairMemory

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original final folding writes only to its real accumulator and SHA
buffers; the decrement happens before the checked input subrange is used. -/
theorem fold_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (roots acc stp accel query : BitVec 64) (k : Nat) (positive : 0<k) (inside : k≤15)
    (workspace : ShaPair.Workspace source stp accel)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k))))
    (rootsArena : AllocatedBytes.Arena roots 768) (accArena : AllocatedBytes.Arena acc 32)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96)
    (accAway : CopyGeneral.Away acc query 32)
    (run : evaluateHOLFiniteState source foldStep=(none,post)) : post.memory query=source.memory query := by
  let entry := bind source "k" (BitVec.ofNat 64 (k-1))
  have assigned := StateSteps.assign_execute source "k" decrementExpression (BitVec.ofNat 64 k) (BitVec.ofNat 64 (k-1)) round (decrement_read source k positive (by omega) round)
  rw [fold_shape.2.1,StateSteps.next_sequence source entry decrement _ assigned (Nat.le_refl _)] at run
  have args := fold_arguments entry roots acc (k-1)
    ((bind_lookup_other source "k" "roots" (BitVec.ofNat 64 (k-1)) (by decide)).trans root)
    ((bind_lookup_other source "k" "acc" (BitVec.ofNat 64 (k-1)) (by decide)).trans accumulator) (bind_lookup_same _ _ _)
  exact ShaPair.call_memory entry post (roots+BitVec.ofNat 64 (32*(k-1))) acc acc stp accel query
    (ShaPair.Workspace.of_fields source entry stp accel workspace rfl rfl rfl rfl)
    (AllocatedBytes.Arena.subrange roots 768 (32*(k-1)) 32 rootsArena (by omega)) accArena stateAway accelAway accAway foldArguments args run

/-- Every real normal fold iteration retains its bounded root index and
protects arbitrary decoded words outside the accumulator and SHA buffers. -/
theorem fold_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (roots acc stp accel query : BitVec 64) (k : Nat) (inside : k≤15)
    (workspace : ShaPair.Workspace source stp accel)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k))))
    (rootsArena : AllocatedBytes.Arena roots 768) (accArena : AllocatedBytes.Arena acc 32)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96)
    (accAway : CopyGeneral.Away acc query 32)
    (run : evaluateHOLFiniteState source foldLoop=(none,post)) : post.memory query=source.memory query := by
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → foldValid roots acc stp accel current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) foldTest=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) foldStep=(none,target) →
      foldValid roots acc stp accel target ∧ target.memory query=current.memory query := by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨position,bounded,currentK,currentRoots,currentAcc,currentWorkspace⟩ := ready
    have expected := fold_test_read current position bounded currentK
    have active : 0<position := by
      by_contra inactive
      have zero : position=0 := by omega
      rw [if_pos zero] at expected
      have wordZero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero wordZero
    have entryWorkspace := ShaPair.Workspace.of_fields current (decClockHOLFinite current) stp accel currentWorkspace rfl rfl rfl rfl
    have memory := fold_step_memory (decClockHOLFinite current) target roots acc stp accel query position active bounded entryWorkspace currentRoots currentAcc currentK rootsArena accArena stateAway accelAway accAway bodyRun
    have nextK := fold_advances (decClockHOLFinite current) target position active (by omega) currentK bodyRun
    have other (name : String) (different : ofString name≠ofString "k") : target.locals.lookup (ofString name)=current.locals.lookup (ofString name) := by
      have summary := (fold_other (ofString name) different).summary_full (decClockHOLFinite current)
      unfold LocalSummary at summary
      rw [bodyRun] at summary
      exact summary.1 rfl
    have nextWorkspace := ShaPair.Workspace.after (decClockHOLFinite current) target stp accel entryWorkspace foldStep none bodyRun
      (fold_globals (ofString "sha_st") current.code currentWorkspace.installed) (fold_globals (ofString "sha_accel") current.code currentWorkspace.installed)
    exact ⟨⟨position-1,by omega,nextK,(other "roots" (by decide)).trans currentRoots,(other "acc" (by decide)).trans currentAcc,nextWorkspace⟩,memory⟩
  rw [fold_shape.1] at run
  exact MemoryAt.loop_normal source.code (ofString "roots") foldTest foldStep query
    (fun current=>(fold_other (ofString "roots") (by decide)).summary_full current)
    (foldValid roots acc stp accel) transition source post rfl ⟨k,inside,round,root,accumulator,workspace⟩ run

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.fold_step_memory
#print axioms InitECandidate.Solver.Input.Progressive.fold_loop_memory
