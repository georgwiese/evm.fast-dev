import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalCost
import InitECandidate.Solver.Input.CurrentHash.FixedRecordMemory
import InitECandidate.Solver.Input.CurrentHash.MemoryContextTransport

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem step_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros query : BitVec 64) (n index : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : RoundState source p roots n index) (active : index<n)
    (inputArena : AllocatedBytes.Arena p (44*n)) (rootsArena : AllocatedBytes.Arena roots (32*n)) (rootsAway : CopyGeneral.Away roots query (32*n))
    (actual : evaluateHOLFiniteState source withdrawalStep=(none,post)) : post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query := by
  rw [loop_shapes.2.2.2] at actual
  obtain ⟨middle,normal,advanced⟩ := Input.sequence_none source post _ increment actual
  have inputRange : 44*index+44≤44*n := by omega
  have input := AllocatedBytes.Arena.subrange p (44*n) (44*index) 44 inputArena inputRange
  have output := AllocatedBytes.Arena.subrange roots (32*n) (32*index) 32 rootsArena (by omega)
  have away := CopyGeneral.Away.subrange roots query (32*n) (32*index) 32 rootsAway (by omega)
  have frame := FixedRecord.call_frame .withdrawal source middle (p+BitVec.ofNat 64 (44*index)) cursor (roots+BitVec.ofNat 64 (32*index)) zeros query
    context input output away withdrawalArguments (arguments_read source p roots n index data) normal
  have nextContext := context.after_call .htr_withdrawal withdrawalArguments frame.2 normal
  have kept := CallNormal.ignored_lookup source middle (ofString "i") (ofString "htr_withdrawal") withdrawalArguments normal
  have position := kept.trans data.position
  have read : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,position,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have endpoint := assign_none middle post "i" _ (BitVec.ofNat 64 (index+1)) read advanced
  rw [endpoint]
  exact ⟨frame.1,nextContext.of_frozen rfl⟩

/-- Complete actual current withdrawal loop preserves protected caller
metadata and restores the same heap at every real continuing iteration. -/
theorem loop_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros query : BitVec 64) (n index : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : RoundState source p roots n index)
    (bounded : n≤134217728) (inside : index≤n)
    (inputArena : AllocatedBytes.Arena p (44*n)) (rootsArena : AllocatedBytes.Arena roots (32*n)) (rootsAway : CopyGeneral.Away roots query (32*n))
    (actual : evaluateHOLFiniteState source withdrawalLoop=(none,post)) :
    post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query ∧ valid p roots n post := by
  let invariant (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
    MerkleMemory.Context state cursor zeros query ∧ ∃ position, position≤n ∧ RoundState state p roots n position ∧ state.memory query=source.memory query
  have final : invariant post := by
    rw [loop_shapes.2.2.1] at actual
    apply loop_invariant_no_control source.code withdrawalTest withdrawalStep
      (fun current=>((withdrawal_step_local (ofString "nwd") (by decide)).summary_full current).2.2)
      invariant _ source post rfl ⟨context,index,inside,data,rfl⟩ actual
    intro current codeEq ready word read nonzero funded target continued
    obtain ⟨currentContext,position,positionBound,currentData,kept⟩ := ready
    have active := active_of_test current p roots n position bounded positionBound currentData word read nonzero
    have frame := step_frame (decClockHOLFinite current) target p roots cursor zeros query n position
      (currentContext.of_frozen rfl) currentData.dec_clock active inputArena rootsArena rootsAway continued
    have next := step_normal (decClockHOLFinite current) target p roots n position currentData.dec_clock continued
    exact ⟨frame.2,position+1,by omega,next,frame.1.trans kept⟩
  obtain ⟨context,position,positionBound,data,kept⟩ := final
  exact ⟨kept,context,position,positionBound,data⟩

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.step_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.loop_frame
