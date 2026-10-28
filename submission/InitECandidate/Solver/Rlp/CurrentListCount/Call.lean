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
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "rlp_list_count") expressions)).2.clock≤46*length.toNat+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits
  exact ClockCost.call_current source destination (ofString "rlp_list_count") expressions (Header.values pointer length) ListCount.body callee .one (46*length.toNat) args called paid

theorem ignored_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_list_count") expressions)=(none,post)) :
    LocalEffects.erase post=LocalEffects.erase source := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code arena.code)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,value,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post (ofString "rlp_list_count") expressions normal
  have valuesEq:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq:=Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  obtain ⟨count,valueEq,bounded,frame⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits value bodyRun
  rw [endpoint]
  exact frame

/-- Continuation pricing comes only after the actual count return derives
its word, bound and pure caller state; no future count or room is assumed. -/
theorem scoped_valid_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (tail : ∀ count : BitVec 64,∀ clock : Nat,count.toNat≤length.toNat →
      clock-(evaluateHOLFiniteState (bind {source with clock:=clock} name count) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_list_count") expressions continuation)).2.clock≤46*length.toNat+tailPrice+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits
  apply ClockCost.scoped_reached_current source name .one (ofString "rlp_list_count") expressions (Header.values pointer length) ListCount.body continuation callee .one (46*length.toNat) tailPrice args called paid
  intro target value normal checked
  obtain ⟨count,valueEq,bounded,frame⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits value normal
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) frame
  change {target with locals:=source.locals}={source with clock:=target.clock} at callerFrame
  have canonical : CallNormal.continuationEntry source target name value=bind {source with clock:=target.clock} name count := by
    unfold CallNormal.continuationEntry
    rw [callerFrame,valueEq]
    rfl
  rw [canonical]
  exact tail count target.clock bounded

/-- A real normal scoped caller resumes with the actual bounded count and
the same nonlocal state, at the clock of its real child return. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_list_count") expressions continuation)=(some (.returned value),post)) :
    ∃ count : BitVec 64,∃ clock : Nat,∃ inner,count.toNat≤length.toNat ∧ clock≤source.clock ∧ source.clock-clock≤46*length.toNat+1 ∧
      evaluateHOLFiniteState (bind {source with clock:=clock} name count) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code arena.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_normal source post name .one (ofString "rlp_list_count") expressions (Header.values pointer length) ListCount.body continuation callee .one args called value normal
  obtain ⟨count,valueEq,bounded,frame⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits answer bodyRun
  have price:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits
  have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) ListCount.body
  rw [bodyRun] at price forward
  change source.clock-1-target.clock≤46*length.toNat at price
  change target.clock≤source.clock-1 at forward
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) frame
  change {target with locals:=source.locals}={source with clock:=target.clock} at callerFrame
  have canonical : CallNormal.continuationEntry source target name answer=bind {source with clock:=target.clock} name count := by
    unfold CallNormal.continuationEntry
    rw [callerFrame,valueEq]
    rfl
  rw [canonical] at remaining
  exact ⟨count,target.clock,inner,bounded,(by omega),(by omega),remaining,endpoint⟩

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.call_cost
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.ignored_frame
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.scoped_valid_cost
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.scoped_normal
