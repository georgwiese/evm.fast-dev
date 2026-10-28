import InitECandidate.Solver.Input.CurrentHash.RequestListStep
import InitECandidate.Solver.Input.CurrentHash.FixedRecordMemory
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Input.CurrentHash.RequestList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem RoundState.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : Kind} {p roots out : BitVec 64} {n index : Nat}
    (data : RoundState source kind p roots out n index) (function : MlS) (expressions : List (ExpHOL 64))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) function expressions)=(none,post)) : RoundState post kind p roots out n index := by
  have installed : OriginalCode.Installed post.code := by rw [(evaluation_fields source post _ none actual).2.2.2]; exact data.installed
  have kept (name : String) := CallNormal.ignored_lookup source post (ofString name) function expressions actual
  exact ⟨installed,(kept "kind").trans data.category,(kept "p").trans data.pointer,(kept "n").trans data.count,(kept "sz").trans data.size,
    (kept "roots").trans data.root,(kept "out").trans data.output,(kept "i").trans data.position⟩

theorem record_call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots cursor out zeros query : BitVec 64) (n index : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : RoundState source kind p roots out n index) (active : index<n)
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (rootsArena : AllocatedBytes.Arena roots (32*n))
    (rootsAway : CopyGeneral.Away roots query (32*n))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) kind.record.name arguments)=(none,post)) :
    post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query := by
  have inputRange : index*kind.record.length+kind.record.length≤n*kind.record.length := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right kind.record.length (Nat.succ_le_of_lt active)
  have input := AllocatedBytes.Arena.subrange p (n*kind.record.length) (index*kind.record.length) kind.record.length inputArena inputRange
  have output := AllocatedBytes.Arena.subrange roots (32*n) (32*index) 32 rootsArena (by omega)
  have away := CopyGeneral.Away.subrange roots query (32*n) (32*index) 32 rootsAway (by omega)
  have args := arguments_read source kind p roots out n index data
  have frame := FixedRecord.call_frame kind.record source post (p+BitVec.ofNat 64 (index*kind.record.length)) cursor (roots+BitVec.ofNat 64 (32*index)) zeros query
    context input output away arguments args actual
  exact ⟨frame.1,context.after_call kind.record.routine arguments frame.2 actual⟩

theorem branch_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind selected : Kind) (p roots cursor out zeros query : BitVec 64) (n index : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : RoundState source kind p roots out n index) (active : index<n)
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (rootsArena : AllocatedBytes.Arena roots (32*n))
    (rootsAway : CopyGeneral.Away roots query (32*n))
    (actual : evaluateHOLFiniteState source (branch selected)=(none,post)) :
    post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query ∧ RoundState post kind p roots out n index := by
  rw [branch_evaluate source kind selected data.category] at actual
  by_cases same : kind=selected
  · rw [if_pos same] at actual
    have frame := record_call_frame source post kind p roots cursor out zeros query n index context data active inputArena rootsArena rootsAway actual
    exact ⟨frame.1,frame.2,data.after_call _ _ actual⟩
  · rw [if_neg same] at actual
    have endpoint : post=source := (congrArg Prod.snd actual).symm
    rw [endpoint]
    exact ⟨rfl,context,data⟩

/-- The real five-test dispatch preserves metadata and current heap through
its one selected record call and final counter increment. -/
theorem chain_frame (branches : List Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots cursor out zeros query : BitVec 64) (n index : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : RoundState source kind p roots out n index) (active : index<n)
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (rootsArena : AllocatedBytes.Arena roots (32*n))
    (rootsAway : CopyGeneral.Away roots query (32*n))
    (actual : evaluateHOLFiniteState source (chain branches)=(none,post)) : post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query := by
  induction branches generalizing source with
  | nil =>
    have read : eval source (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
      simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,data.position,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
    have endpoint := assign_none source post "i" _ (BitVec.ofNat 64 (index+1)) read actual
    have frame : CeilLog2.frozen post=CeilLog2.frozen source := by rw [endpoint]; rfl
    have memory := congrArg PanSemStateFiniteExact.memory frame
    change post.memory=source.memory at memory
    exact ⟨congrArg (fun memory=>memory query) memory,context.of_frozen frame⟩
  | cons selected rest ih =>
    change evaluateHOLFiniteState source (.seq (branch selected) (chain rest))=(none,post) at actual
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_none source post _ _ actual
    have front := branch_frame source middle kind selected p roots cursor out zeros query n index context data active inputArena rootsArena rootsAway normal
    have back := ih middle front.2.1 front.2.2 remaining
    exact ⟨back.1.trans front.1,back.2⟩

theorem chain_globals (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (branches : List Kind) : GlobalEffects.Preserves (key cursor) code (chain branches) := by
  induction branches with
  | nil => exact GlobalEffects.assign _ code _ _
  | cons selected rest ih =>
    exact GlobalEffects.sequence _ code _ _
      (GlobalEffects.conditional _ code _ _ _ (Effects.call_preserves cursor code installed selected.record.routine (some none) arguments) (GlobalEffects.skip _ code)) ih

theorem loop_globals (cursor : Cursor) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves (key cursor) code loop :=
  GlobalEffects.loop _ code _ _ (chain_globals cursor code installed kinds)

end InitECandidate.Solver.Input.CurrentHash.RequestList

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.RoundState.after_call
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.record_call_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.branch_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.chain_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.chain_globals
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.loop_globals
