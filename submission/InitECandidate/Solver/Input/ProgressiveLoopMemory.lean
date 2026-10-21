import InitECandidate.Solver.Input.ProgressiveStepMemory
import InitECandidate.Solver.Input.ProgressiveLoop

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- All actual normal geometric chunk iterations preserve the protected
word. Each next invariant is derived from that same observed body call. -/
theorem loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p roots cursor zeros stp accel chunk query : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (inside : k≤15)
    (actual : RoundState source p roots cursor zeros stp accel n k)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (mapped : Geometry p roots cursor zeros n) (below : query.toNat<cursor.toNat)
    (rootsAway : CopyGeneral.Away roots query 768)
    (run : evaluateHOLFiniteState source loop=(none,post)) : post.memory query=source.memory query := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    valid p roots cursor zeros stp accel n current ∧ SszHash.Protected current stp accel chunk zeros query
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) step=(none,target) →
      invariant target ∧ target.memory query=current.memory query := by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨⟨position,positionBound,currentRound⟩,currentProtection⟩ := ready
    have expected := test_read current p roots cursor zeros stp accel n position bounded positionBound currentRound
    have active : offset position<n := by
      by_contra inactive
      rw [if_neg inactive] at expected
      have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero zero
    have entryRound := RoundState.dec_clock current p roots cursor zeros stp accel n position currentRound
    have entryProtection := SszHash.Protected.of_fields current (decClockHOLFinite current) stp accel chunk zeros query currentProtection rfl rfl (by intro key other; rfl)
    have nextRound := step_normal (decClockHOLFinite current) target p roots cursor zeros stp accel n position bounded active entryRound mapped bodyRun
    have nextProtection := SszHash.Protected.after (decClockHOLFinite current) target stp accel chunk zeros query entryProtection step none bodyRun
      (fun key other=>step_globals key current.code currentProtection.workspace.sha.installed other)
    have memory := step_memory (decClockHOLFinite current) target p roots cursor zeros stp accel chunk query n position bounded active entryRound entryProtection mapped below rootsAway bodyRun
    exact ⟨⟨⟨position+1,by have limit:=active_round n position bounded active; omega,nextRound⟩,nextProtection⟩,memory⟩
  rw [loop_shape.1] at run
  exact MemoryAt.loop_normal source.code (ofString "p") test step query
    (fun current=>(step_other (ofString "p") (by decide) (by decide) (by decide) (by decide)).summary_full current)
    invariant transition source post rfl ⟨⟨k,inside,actual⟩,protection⟩ run

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.loop_memory
