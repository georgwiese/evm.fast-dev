import InitECandidate.Solver.Rlp.CurrentListCount.ItemsMemory
import InitECandidate.Solver.Rlp.CurrentListCount.Call

namespace InitECandidate.Solver.Rlp.CurrentListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem scoped_normal_items (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_list_count") expressions continuation)=(some (.returned value),post)) :
    ∃ items : List ListItem,∃ count : BitVec 64,∃ clock : Nat,∃ inner,ListItems source pointer length.toNat items ∧ count.toNat=items.length ∧ clock≤source.clock ∧ source.clock-clock≤46*length.toNat+1 ∧
      evaluateHOLFiniteState (bind {source with clock:=clock} name count) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code arena.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_normal source post name .one (ofString "rlp_list_count") expressions (Header.values pointer length) ListCount.body continuation callee .one args called value normal
  obtain ⟨items,count,model,valueEq,countEq,frame⟩ := body_items (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer bodyRun
  have currentItems:=ListItems.transport (callEntryStateHOLFinite source callee) source pointer length.toNat items model length.isLt (by intro offset inside; rfl)
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
  exact ⟨items,count,target.clock,inner,currentItems,countEq,(by omega),(by omega),remaining,endpoint⟩

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.scoped_normal_items
