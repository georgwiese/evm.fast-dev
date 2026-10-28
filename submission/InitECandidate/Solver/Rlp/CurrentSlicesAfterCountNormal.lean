import InitECandidate.Solver.Rlp.SlicesAfterAllocNormal
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.CurrentSlices
open Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The original allocation derives real room for the counted records.
Its actual continuation builds the physical array; only the current heap
cursor, input ownership and input-size arithmetic are entry geometry. -/
theorem after_count_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap count : BitVec 64) (items : List ListItem)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (model : ListItems source pointer length.toNat items) (countEq : count.toNat=items.length)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterCount=(some (.returned value),target)) :
    heap.toNat+16*count.toNat≤2952790016 ∧ value=result heap count ∧ Records target.memory heap pointer items ∧
      target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64)))) ∧
      Window source target heap.toNat (heap.toNat+16*count.toNat) := by
  have countBound := ListItems.count_le source pointer length.toNat items model
  rw [←countEq] at countBound
  have product : (count*16#64).toNat=16*count.toNat := by
    rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by change count.toNat*16<2^64; omega)]
    change count.toNat*16=16*count.toNat
    omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) allocationArguments=
      some (PersistentAlloc.values (count*16#64)) := by
    simp [allocationArguments,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,countCell,valueIsWord,valueWord,panOpHOL]
  rw [after_count_shape] at normal
  obtain ⟨callee,called,amountLocal⟩:=PersistentAlloc.environment source.code.lookup (count*16#64) (PersistentAlloc.original_code source.code installed)
  obtain ⟨funded,calleePost,answer,inner,bodyRun,checked,continuation,restored⟩:=Input.CallNormal.scoped_normal source target "arr" .one (ofString "alloc") allocationArguments (PersistentAlloc.values (count*16#64)) PersistentAlloc.body afterAlloc callee .one args called value normal
  obtain ⟨answerEq,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) calleePost heap (count*16#64) amountLocal heapGlobal heapBound (Input.Trap.original_code source.code installed) answer bodyRun
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  change {calleePost with locals:=source.locals}=PersistentAlloc.post {source with clock:=source.clock-1} heap (count*16#64) at callerFrame
  unfold Input.CallNormal.continuationEntry at continuation
  rw [answerEq,callerFrame] at continuation
  rw [product] at room
  let ready := bind (PersistentAlloc.post {source with clock:=source.clock-1} heap (count*16#64)) "arr" heap
  have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ "arr" "p" _ (by decide)).trans pointerCell
  have readyCount : ready.locals.lookup (ofString "count")=some (.val (.word count)) :=
    (bind_lookup_other _ "arr" "count" _ (by decide)).trans countCell
  have readyItems := ListItems.transport source ready pointer length.toNat items model length.isLt (by intro offset inside; rfl)
  obtain ⟨answer,records,globals,frame⟩ := after_alloc_normal ready inner pointer length heap count items readyPointer (bind_lookup_same _ _ _) readyCount
    readyItems countEq before (by omega) installed value continuation
  refine ⟨room,answer,?_,?_,?_⟩
  · rw [restored]
    exact records
  · rw [restored]
    exact globals
  · intro query outside
    rw [restored]
    exact frame query outside

end InitECandidate.Solver.Rlp.CurrentSlices

#print axioms InitECandidate.Solver.Rlp.CurrentSlices.after_count_normal
