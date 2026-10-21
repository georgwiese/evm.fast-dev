import InitECandidate.Solver.Input.PayloadHashWithdrawalLoop
import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Input.PayloadHash.Withdrawals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The real withdrawal hash/counter body preserves any protected input
word below its roots array, independently of row or digest values. -/
theorem step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p roots cursor stp accel chunk zeros query : BitVec 64) (n index : Nat)
    (actual : RoundState source p roots cursor stp accel chunk zeros n index)
    (geometry : Geometry p roots cursor n) (active : index<n)
    (protection : SszHash.Protected source stp accel chunk zeros query) (below : query.toNat<roots.toNat)
    (run : evaluateHOLFiniteState source withdrawalStep=(none,post)) : post.memory query=source.memory query := by
  rw [loop_shapes.2.2.2] at run
  obtain ⟨middle,called,advanced⟩ := sequence_none source post _ increment run
  obtain ⟨inputArena,outArena⟩ := call_geometry p roots cursor n index geometry active
  have rootsAway := CopyGeneral.Away.after roots query (32*n) geometry.rootsAligned (by have h:=geometry.rootsArena.upper; omega) below
  have cursorBelow : query.toNat<cursor.toNat := by have h:=geometry.rootsBefore; omega
  have front := FixedHash.call_memory .withdrawal source middle (p+BitVec.ofNat 64 (44*index)) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros query
    protection actual.heap inputArena geometry.temporaryArena geometry.aligned outArena cursorBelow
    (CopyGeneral.Away.subrange roots query (32*n) (32*index) 32 rootsAway (by omega)) withdrawalArguments
    (arguments_read source p roots cursor stp accel chunk zeros n index actual) called
  have tail := MemoryAt.assign_current middle .local (ofString "i") (.op .add [localVar "i",.const 1#64]) query
  change (evaluateHOLFiniteState middle increment).2.memory query=middle.memory query at tail
  rw [advanced] at tail
  exact tail.trans front

/-- Whole original withdrawal loop preserves protected decoded/input words
on a genuine normal exit, with no assumption about future hash success. -/
theorem loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p roots cursor stp accel chunk zeros query : BitVec 64) (n index : Nat)
    (inside : index≤n) (actual : RoundState source p roots cursor stp accel chunk zeros n index)
    (geometry : Geometry p roots cursor n)
    (protection : SszHash.Protected source stp accel chunk zeros query) (below : query.toNat<roots.toNat)
    (run : evaluateHOLFiniteState source withdrawalLoop=(none,post)) : post.memory query=source.memory query := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>valid p roots cursor stp accel chunk zeros n current ∧ SszHash.Protected current stp accel chunk zeros query
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) withdrawalTest=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) withdrawalStep=(none,target) → invariant target ∧ target.memory query=current.memory query := by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨⟨position,positionBound,currentRound⟩,currentProtection⟩ := ready
    have active := active_of_test current p roots cursor stp accel chunk zeros n position geometry.countBound positionBound currentRound word read nonzero
    have entryRound := RoundState.dec_clock current p roots cursor stp accel chunk zeros n position currentRound
    have entryProtection := currentProtection.with_workspace current (decClockHOLFinite current) stp accel chunk zeros query entryRound.workspace
    have next := step_normal (decClockHOLFinite current) target p roots cursor stp accel chunk zeros n position entryRound geometry active bodyRun
    have nextProtection := currentProtection.with_workspace current target stp accel chunk zeros query next.workspace
    have memory := step_memory (decClockHOLFinite current) target p roots cursor stp accel chunk zeros query n position entryRound geometry active entryProtection below bodyRun
    exact ⟨⟨⟨position+1,by omega,next⟩,nextProtection⟩,memory⟩
  rw [loop_shapes.2.2.1] at run
  exact MemoryAt.loop_normal source.code (ofString "wd") withdrawalTest withdrawalStep query
    (fun current=>(withdrawal_step_local (ofString "wd") (by decide)).summary_full current) invariant transition source post rfl ⟨⟨index,inside,actual⟩,protection⟩ run

end InitECandidate.Solver.Input.PayloadHash.Withdrawals

#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.step_memory
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.loop_memory
