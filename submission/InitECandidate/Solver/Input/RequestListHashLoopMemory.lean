import InitECandidate.Solver.Input.FixedHashMemory
import InitECandidate.Solver.Input.RequestListHashLoop

namespace InitECandidate.Solver.Input.RequestListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real selected record call preserves decoded words outside the actual
root array and below temporary storage. No record hash values are assumed. -/
theorem branch_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind selected : Kind)
    (p roots out cursor stp accel chunk zeros query : BitVec 64) (n index : Nat)
    (active : index<n) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index)
    (protection : SszHash.Protected source stp accel chunk zeros query) (geometry : Geometry kind p roots cursor n)
    (below : query.toNat<cursor.toNat) (rootsAway : CopyGeneral.Away roots query (32*n))
    (run : evaluateHOLFiniteState source (branch selected)=(none,post)) : post.memory query=source.memory query := by
  rw [branch_evaluate source kind selected actual.category] at run
  by_cases same : kind=selected
  · rw [if_pos same] at run
    obtain ⟨inputArena,outArena,outAligned,temporary⟩ := iteration_geometry kind p roots cursor n index active geometry
    exact FixedHash.call_memory kind.record source post (p+BitVec.ofNat 64 (index*kind.record.length)) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros query
      protection actual.heap inputArena temporary geometry.aligned outArena below
      (CopyGeneral.Away.subrange roots query (32*n) (32*index) 32 rootsAway (by omega)) arguments
      (arguments_read source kind p roots out cursor stp accel chunk zeros n index actual) run
  · rw [if_neg same] at run
    have endpoint : post=source := (congrArg Prod.snd run).symm
    rw [endpoint]

theorem chain_memory (branches : List Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (p roots out cursor stp accel chunk zeros query : BitVec 64) (n index : Nat)
    (active : index<n) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index)
    (protection : SszHash.Protected source stp accel chunk zeros query) (geometry : Geometry kind p roots cursor n)
    (below : query.toNat<cursor.toNat) (rootsAway : CopyGeneral.Away roots query (32*n))
    (run : evaluateHOLFiniteState source (chain branches)=(none,post)) : post.memory query=source.memory query := by
  induction branches generalizing source post with
  | nil=>
    have frame := MemoryAt.assign_current source .local (ofString "i") (.op .add [localVar "i",.const 1#64]) query
    change evaluateHOLFiniteState source increment=(none,post) at run
    change (evaluateHOLFiniteState source increment).2.memory query=source.memory query at frame
    rw [run] at frame
    exact frame
  | cons selected rest ih=>
    change evaluateHOLFiniteState source (.seq (branch selected) (chain rest))=(none,post) at run
    obtain ⟨middle,normal,remaining⟩ := sequence_none source post _ _ run
    have front := branch_memory source middle kind selected p roots out cursor stp accel chunk zeros query n index active actual protection geometry below rootsAway normal
    have next := (branch_summary source middle kind selected p roots out cursor stp accel chunk zeros n index active actual geometry none normal (by simp)).2 rfl
    have nextProtection := protection.with_workspace source middle stp accel chunk zeros query next.workspace
    exact (ih middle post next nextProtection remaining).trans front

/-- The original variable request-record loop preserves protected decoded
memory at every real normal iteration, retaining its actual kind and index. -/
theorem loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (p roots out cursor stp accel chunk zeros query : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n)
    (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index)
    (protection : SszHash.Protected source stp accel chunk zeros query) (geometry : Geometry kind p roots cursor n)
    (below : query.toNat<cursor.toNat) (rootsAway : CopyGeneral.Away roots query (32*n))
    (run : evaluateHOLFiniteState source loop=(none,post)) : post.memory query=source.memory query := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>valid kind p roots out cursor stp accel chunk zeros n current ∧ SszHash.Protected current stp accel chunk zeros query
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) step=(none,target) →
      invariant target ∧ target.memory query=current.memory query := by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨⟨position,positionBound,currentRound⟩,currentProtection⟩ := ready
    have active := active_of_test current kind p roots out cursor stp accel chunk zeros n position bounded positionBound currentRound word read nonzero
    have entryRound := RoundState.dec_clock current kind p roots out cursor stp accel chunk zeros n position currentRound
    have entryProtection := currentProtection.with_workspace current (decClockHOLFinite current) stp accel chunk zeros query entryRound.workspace
    have next := step_normal (decClockHOLFinite current) target kind p roots out cursor stp accel chunk zeros n position active entryRound geometry bodyRun
    have nextProtection := currentProtection.with_workspace current target stp accel chunk zeros query next.workspace
    have frame := chain_memory kinds (decClockHOLFinite current) target kind p roots out cursor stp accel chunk zeros query n position active entryRound entryProtection geometry below rootsAway bodyRun
    exact ⟨⟨⟨position+1,by omega,next⟩,nextProtection⟩,frame⟩
  exact MemoryAt.loop_normal source.code (ofString "p") test step query
    (fun current=>(chain_local (ofString "p") kinds (by decide)).summary_full current) invariant transition source post rfl ⟨⟨index,inside,actual⟩,protection⟩ run

end InitECandidate.Solver.Input.RequestListHash

#print axioms InitECandidate.Solver.Input.RequestListHash.branch_memory
#print axioms InitECandidate.Solver.Input.RequestListHash.chain_memory
#print axioms InitECandidate.Solver.Input.RequestListHash.loop_memory
