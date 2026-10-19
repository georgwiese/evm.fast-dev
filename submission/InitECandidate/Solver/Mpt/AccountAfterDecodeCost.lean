import InitECandidate.Solver.Mpt.AccountAfterSlicesCost
import InitECandidate.Solver.Rlp.DecodeNormalFrame
import InitECandidate.Solver.Rlp.SlicesNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Real complete decoded extent supplies the payload span for original
list conversion; its actual normal result supplies all physical records
needed by the four-field decoder. All stopped outcomes remain priced. -/
theorem after_decode_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out : BitVec 64) (cutoff : Nat) (value : ValueHOL 64)
    (itemCell : source.locals.lookup (ofString "it")=some value) (complete : Rlp.Decode.Complete pointer length value)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterDecode).2.clock≤131*length.toNat+247 := by
  obtain ⟨header,payload,flag,valueEq,head,positive,extent,binary,listHead⟩ := complete
  rw [valueEq] at itemCell
  have pointerNumber : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by have := heap.isLt; omega)
  have payloadFits : (pointer+header).toNat+payload.toNat<2^64 := by rw [pointerNumber]; have := heap.isLt; omega
  have payloadBefore : (pointer+header).toNat+payload.toNat≤heap.toNat := by rw [pointerNumber]; omega
  have payloadAbove : cutoff≤(pointer+header).toNat := by rw [pointerNumber]; omega
  have payloadSmall : 16*payload.toNat<2^64 := by omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [field "it" 1,field "it" 2]=
      some (Rlp.Header.values (pointer+header) payload) := by
    simp [field,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result]
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") Rlp.Slices.body Rlp.Slices.resultShape
    (pointer+header) payload (Rlp.Slices.original_code source.code installed)
  have entryArena := Rlp.Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have bodyPrice := Rlp.Slices.body_cost (callEntryStateHOLFinite source callee) (pointer+header) payload cursor limit pointerLocal lengthLocal entryArena payloadFits installed
  have callerPrice := Input.ClockCost.scoped_reached_current source "sl" Rlp.Slices.resultShape (ofString "rlp_list_to_slices") [field "it" 1,field "it" 2] _
    Rlp.Slices.body afterSlices callee Rlp.Slices.resultShape (71*payload.toNat+34) (60*payload.toNat+212) args called bodyPrice ?_
  · rw [after_decode_shape]
    have fullPrice := Fail.guard_reached_cost source (.cmp .notEqual (field "it" 0) (.const 1#64)) 20#64
      (.decCall (ofString "sl") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") [field "it" 1,field "it" 2] afterSlices)
      (131*length.toNat+247) installed (by intro passed; omega)
    simpa only [fail] using fullPrice.trans (by omega)
  · intro post answer bodyRun checked
    obtain ⟨items,count,itemModel,countEq,countBound,answerEq,records,room,nextArena,nextHeap,frame,price⟩ :=
      Rlp.Slices.body_normal (callEntryStateHOLFinite source callee) post (pointer+header) payload heap cursor limit cutoff pointerLocal lengthLocal
        entryArena heapGlobal heapBound payloadBefore payloadSmall aligned scratchBelow payloadAbove installed answer bodyRun
    rw [answerEq]
    let ready := Input.CallNormal.continuationEntry source post "sl" (Rlp.Slices.result heap count)
    have readyItems := Rlp.ListItems.transport post ready (pointer+header) payload.toNat items itemModel payload.isLt (by intro offset inside; rfl)
    have readyArena := Rlp.Validation.Arena.of_fields post ready cursor limit nextArena rfl rfl
    have currentOutput := (Input.CallNormal.continuation_lookup_other source post "sl" "acct_out" (Rlp.Slices.result heap count) (by decide)).trans outputCell
    have fields := Input.evaluation_fields (callEntryStateHOLFinite source callee) post Rlp.Slices.body (some (.returned answer)) bodyRun
    have currentInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed post.code; rw [fields.2.2.2]; exact installed
    exact after_slices_cost ready heap (pointer+header) payload cursor limit out count cutoff items
      (Input.CallNormal.continuation_lookup_same source post "sl" (Rlp.Slices.result heap count)) currentOutput readyArena readyItems records countEq
      payloadFits payloadBefore room aligned scratchBelow payloadAbove output currentInstalled

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_decode_cost
