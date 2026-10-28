import InitECandidate.Solver.Input.CurrentHash.RequestListMemoryStep
import InitECandidate.Solver.Input.CurrentHash.RequestListLoop

namespace InitECandidate.Solver.Input.CurrentHash.RequestList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every actual normal record-list iteration keeps the same decoded inputs,
protected metadata and entering heap. Its next index comes from that run. -/
theorem loop_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots cursor out zeros query : BitVec 64) (n index : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : RoundState source kind p roots out n index)
    (bounded : n≤134217728) (inside : index≤n)
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (rootsArena : AllocatedBytes.Arena roots (32*n))
    (rootsAway : CopyGeneral.Away roots query (32*n))
    (actual : evaluateHOLFiniteState source loop=(none,post)) :
    post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query ∧
      ∃ position, position≤n ∧ RoundState post kind p roots out n position := by
  let invariant (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
    MerkleMemory.Context state cursor zeros query ∧ ∃ position, position≤n ∧ RoundState state kind p roots out n position ∧ state.memory query=source.memory query
  have final : invariant post := by
    apply loop_invariant_no_control source.code test step
      (fun current=>((chain_local (ofString "n") kinds (by decide)).summary_full current).2.2)
      invariant _ source post rfl ⟨context,index,inside,data,rfl⟩ actual
    intro current codeEq ready word read nonzero funded target continued
    obtain ⟨currentContext,position,positionBound,currentData,kept⟩ := ready
    have active := active_of_test current kind p roots out n position bounded positionBound currentData word read nonzero
    have frame := chain_frame kinds (decClockHOLFinite current) target kind p roots cursor out zeros query n position
      (currentContext.of_frozen rfl) (RoundState.dec_clock current kind p roots out n position currentData) active inputArena rootsArena rootsAway continued
    have next := step_normal (decClockHOLFinite current) target kind p roots out n position active (RoundState.dec_clock current kind p roots out n position currentData) continued
    exact ⟨frame.2,position+1,by omega,next,frame.1.trans kept⟩
  obtain ⟨context,position,positionBound,data,kept⟩ := final
  exact ⟨kept,context,position,positionBound,data⟩

end InitECandidate.Solver.Input.CurrentHash.RequestList

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.loop_frame
