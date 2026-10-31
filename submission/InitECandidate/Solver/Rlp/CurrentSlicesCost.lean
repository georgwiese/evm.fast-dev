import InitECandidate.Solver.Rlp.SlicesLoopProgram
import InitECandidate.Solver.Rlp.CurrentListCount.Call
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Rlp.CurrentSlices
open Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_alloc_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterAlloc).2.clock≤11*count.toNat := by
  let indexed := bind source "i" 0#64
  let ready := bind indexed "off" 0#64
  have currentIndex : ready.locals.lookup (ofString "i")=some (.val (.word 0#64)) :=
    (bind_lookup_other _ "off" "i" _ (by decide)).trans (bind_lookup_same _ _ _)
  have currentCount : ready.locals.lookup (ofString "count")=some (.val (.word count)) :=
    (bind_lookup_other _ "off" "count" _ (by decide)).trans ((bind_lookup_other _ "i" "count" _ (by decide)).trans countCell)
  have countNat : ready.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 count.toNat))) := by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using currentCount
  have loopPrice := Input.CounterFlow.loop_cost source.code (ofString "i") (ofString "count") loopBody 10 count.toNat count.isLt
    (loop_body_price source.code installed) loop_body_advances loop_body_safe ready 0#64 rfl currentIndex countNat (Nat.zero_le _)
  change ready.clock-(evaluateHOLFiniteState ready (.while condition loopBody)).2.clock≤11*(count.toNat-0) at loopPrice
  rw [←loop_shape,Nat.sub_zero] at loopPrice
  have tail := Input.ClockCost.sequence_current ready loop returnArray (11*count.toNat) 0 loopPrice (Input.ClockCost.returned source.code _)
  have offDecl := Input.ClockCost.declared_current indexed "off" (.const 0#64) 0#64 _ (11*count.toNat) rfl tail
  rw [after_alloc_shape]
  exact Input.ClockCost.declared_current source "i" (.const 0#64) 0#64 _ (11*count.toNat) rfl offDecl

theorem after_count_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterCount).2.clock≤11*count.toNat+2 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) allocationArguments=
      some (WitnessRadix.PersistentAlloc.values (count*16#64)) := by
    simp [allocationArguments,WitnessRadix.PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,countCell,valueIsWord,valueWord,panOpHOL]
  obtain ⟨callee,called,amountLocal⟩ := WitnessRadix.PersistentAlloc.environment source.code.lookup (count*16#64) (WitnessRadix.PersistentAlloc.original_code source.code installed)
  rw [after_count_shape]
  have actual := Input.ClockCost.scoped_reached_current source "arr" .one (ofString "alloc") allocationArguments _ WitnessRadix.PersistentAlloc.body afterAlloc callee .one 1 (11*count.toNat) args called
    (WitnessRadix.PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl) ?_
  · omega
  · intro calleePost returned bodyRun checked
    let ready := Input.CallNormal.continuationEntry source calleePost "arr" returned
    have currentCount : ready.locals.lookup (ofString "count")=some (.val (.word count)) := by
      simpa [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "arr"≠ofString "count" from by decide] using countCell
    have codeEq := (Input.evaluation_fields (callEntryStateHOLFinite source callee) calleePost WitnessRadix.PersistentAlloc.body (some (.returned returned)) bodyRun).2.2.2
    exact after_alloc_cost ready count currentCount (by change Input.OriginalCode.Installed calleePost.code; rw [codeEq]; exact installed)

/-- Complete unchanged current list-to-slices body, including validated count,
allocation and the actual fixed-count unchecked/store loop. Every outcome
costs<=71*length+3 source ticks, without a future array/helper model. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤71*length.toNat+3 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") ListCount.body .one pointer length (ListCount.original_code source.code installed)
  rw [body_shape]
  have actual := Input.ClockCost.scoped_reached_current source "count" .one (ofString "rlp_list_count") arguments _ ListCount.body afterCount callee .one (60*length.toNat) (11*length.toNat+2) args called
    (CurrentListCount.body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits) ?_
  · omega
  · intro calleePost returned bodyRun checked
    obtain ⟨count,valueEq,bounded,metadata,outside⟩ := CurrentListCount.body_normal (callEntryStateHOLFinite source callee) calleePost pointer length pointerLocal lengthLocal
      (arena.of_frame rfl) fits returned bodyRun
    rw [valueEq]
    let ready := bind {calleePost with locals:=source.locals} "count" count
    have currentCount : ready.locals.lookup (ofString "count")=some (.val (.word count)) := bind_lookup_same _ _ _
    have codeEq := (Input.evaluation_fields (callEntryStateHOLFinite source callee) calleePost ListCount.body (some (.returned returned)) bodyRun).2.2.2
    have priced := after_count_cost ready count currentCount (by change Input.OriginalCode.Installed calleePost.code; rw [codeEq]; exact installed)
    change calleePost.clock-(evaluateHOLFiniteState ready afterCount).2.clock≤_ at priced ⊢
    omega

end InitECandidate.Solver.Rlp.CurrentSlices

#print axioms InitECandidate.Solver.Rlp.CurrentSlices.after_alloc_cost
#print axioms InitECandidate.Solver.Rlp.CurrentSlices.after_count_cost
#print axioms InitECandidate.Solver.Rlp.CurrentSlices.body_cost
