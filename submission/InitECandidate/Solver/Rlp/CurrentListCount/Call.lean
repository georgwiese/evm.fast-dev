import InitECandidate.Solver.Rlp.CurrentListCount.Memory
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.CurrentListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "rlp_list_count") expressions)).2.clock≤60*length.toNat+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits
  exact ClockCost.call_current source destination (ofString "rlp_list_count") expressions (Header.values pointer length) ListCount.body callee .one (60*length.toNat) args called paid

theorem ignored_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_list_count") expressions)=(none,post)) :
    MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      Validation.Outside source post 2952790016 2965299200 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code arena.code)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,value,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post (ofString "rlp_list_count") expressions normal
  have valuesEq:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq:=Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  obtain ⟨count,valueEq,bounded,metadata,outside⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits value bodyRun
  rw [endpoint]
  exact ⟨metadata,⟨outside.runtime,fun query outsideQuery=>outside query outsideQuery⟩⟩

/-- Continuation pricing comes only after the actual count return derives
its word, bound and protected caller state; no future count or room is assumed. -/
theorem scoped_valid_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ count : BitVec 64,
      MemoryMetadata.erase current=MemoryMetadata.erase source → Validation.Outside source current 2952790016 2965299200 →
      count.toNat≤length.toNat →
      current.clock-(evaluateHOLFiniteState (bind {current with locals:=source.locals} name count) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_list_count") expressions continuation)).2.clock≤60*length.toNat+tailPrice+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits
  apply ClockCost.scoped_reached_current source name .one (ofString "rlp_list_count") expressions (Header.values pointer length) ListCount.body continuation callee .one (60*length.toNat) tailPrice args called paid
  intro target value normal checked
  obtain ⟨count,valueEq,bounded,metadata,outside⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits value normal
  rw [valueEq]
  exact tail target count metadata ⟨outside.runtime,fun query outsideQuery=>outside query outsideQuery⟩ bounded

/-- A real normal scoped caller resumes with the actual bounded count and
its actual returned memory and retained runtime, at the real child clock. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_list_count") expressions continuation)=(some (.returned value),post)) :
    ∃ count : BitVec 64,∃ calleePost inner,count.toNat≤length.toNat ∧ calleePost.clock≤source.clock ∧ source.clock-calleePost.clock≤60*length.toNat+1 ∧
      MemoryMetadata.erase calleePost=MemoryMetadata.erase source ∧ Validation.Outside source calleePost 2952790016 2965299200 ∧
      evaluateHOLFiniteState (bind {calleePost with locals:=source.locals} name count) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code arena.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_normal source post name .one (ofString "rlp_list_count") expressions (Header.values pointer length) ListCount.body continuation callee .one args called value normal
  obtain ⟨count,valueEq,bounded,metadata,outside⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits answer bodyRun
  have price:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits
  have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) ListCount.body
  rw [bodyRun] at price forward
  change source.clock-1-target.clock≤60*length.toNat at price
  change target.clock≤source.clock-1 at forward
  rw [valueEq] at remaining
  exact ⟨count,target,inner,bounded,(by omega),(by omega),metadata,
    ⟨outside.runtime,fun query outsideQuery=>outside query outsideQuery⟩,remaining,endpoint⟩

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.call_cost
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.ignored_frame
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.scoped_valid_cost
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.scoped_normal
