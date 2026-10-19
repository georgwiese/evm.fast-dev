import InitECandidate.Solver.Mpt.AccountAfterSlicesNormal
import InitECandidate.Solver.Rlp.DecodeNormalFrame
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- The actual list/type/count path derives four records, exactly64 bytes
of record allocation, the current field-call view and the genuine field run.
The combined frame excludes only scratch and those actual fresh records. -/
theorem after_decode_fields (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out : BitVec 64) (cutoff : Nat) (value : ValueHOL 64)
    (itemCell : source.locals.lookup (ofString "it")=some value) (complete : Rlp.Decode.Complete pointer length value)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterDecode=(some (.returned returned),post)) :
    ∃ header payload items ready inner,
      header.toNat+payload.toNat=length.toNat ∧ value=Rlp.Item.result pointer header payload 1#64 ∧ items.length=4 ∧ heap.toNat+64≤33806089496 ∧
      FieldsView ready heap (pointer+header) payload cursor limit out cutoff items ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat → ready.memory query=source.memory query) ∧
      evaluateHOLFiniteState ready fields=(some (.returned returned),inner) ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite inner := by
  obtain ⟨header,payload,flag,valueEq,head,positive,extent,binary,listHead⟩ := complete
  rw [valueEq] at itemCell
  rw [after_decode_shape] at normal
  have safe : Input.LocalPrefix (ofString "acct_out") (.ite (.cmp .notEqual (field "it" 0) (.const 1#64)) (fail 20#64) .skip) :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle,guardRun,tailRun,localEq⟩ := safe.normal_continue source post
    (.decCall (ofString "sl") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") [field "it" 1,field "it" 2] afterSlices) returned normal
  obtain ⟨passed,middleEq⟩ := Fail.guard_normal source middle _ [.const 20#64] installed guardRun
  subst middle
  have flagRead : eval source (field "it" 0)=some (.val (.word flag)) := by
    simp [field,eval,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result]
  have flagOne := Input.CompareFacts.not_equal_zero source (field "it" 0) (.const 1#64) flag 1#64 flagRead rfl passed
  subst flag
  have pointerNumber : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by have := heap.isLt; omega)
  have payloadFits : (pointer+header).toNat+payload.toNat<2^64 := by rw [pointerNumber]; have := heap.isLt; omega
  have payloadBefore : (pointer+header).toNat+payload.toNat≤heap.toNat := by rw [pointerNumber]; omega
  have payloadAbove : cutoff≤(pointer+header).toNat := by rw [pointerNumber]; omega
  have payloadSmall : 16*payload.toNat<2^64 := by omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [field "it" 1,field "it" 2]=
      some (Rlp.Header.values (pointer+header) payload) := by
    simp [field,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result]
  obtain ⟨positive,calleePost,items,count,innerSlices,model,countEq,countBound,records,room,nextArena,codeEq,domain,endian,nextHeap,frame,price,afterSlicesRun,restored⟩ :=
    Rlp.Slices.scoped_normal source post (pointer+header) payload heap cursor limit cutoff "sl" [field "it" 1,field "it" 2] afterSlices args
      arena heapGlobal heapBound payloadBefore payloadSmall aligned scratchBelow payloadAbove installed returned tailRun
  let readySlices := Input.CallNormal.continuationEntry source calleePost "sl" (Rlp.Slices.result heap count)
  have currentModel := Rlp.ListItems.transport calleePost readySlices (pointer+header) payload.toNat items model payload.isLt (by intro offset inside; rfl)
  have currentOutput := (Input.CallNormal.continuation_lookup_other source calleePost "sl" "acct_out" (Rlp.Slices.result heap count) (by decide)).trans outputCell
  have currentArena := Rlp.Validation.Arena.of_fields calleePost readySlices cursor limit nextArena rfl rfl
  have currentInstalled : Input.OriginalCode.Installed readySlices.code := by change Input.OriginalCode.Installed calleePost.code; rw [codeEq]; exact installed
  obtain ⟨countFour,lengthFour,inner,view,fieldsRun,fieldsRestored⟩ := after_slices_fields readySlices innerSlices heap (pointer+header) payload cursor limit out count cutoff items
    (Input.CallNormal.continuation_lookup_same _ _ _ _) currentOutput currentArena currentModel records countEq payloadFits payloadBefore room
    aligned scratchBelow payloadAbove output currentInstalled returned afterSlicesRun
  let ready := bind readySlices "arr" heap
  have fixedAmount : count*16#64=64#64 := by rw [countFour]; decide
  have countNumber : count.toNat=4 := by rw [countFour]; rfl
  have recordRoom : heap.toNat+64≤33806089496 := by rw [countNumber] at room; omega
  refine ⟨header,payload,items,ready,inner,extent,valueEq,lengthFour,recordRoom,view,?_,domain,endian,codeEq,?_,fieldsRun,?_⟩
  · change calleePost.globals.lookup (ofString "heap_ptr")=_
    simpa only [fixedAmount] using nextHeap
  · intro query beyond outside
    change calleePost.memory query=source.memory query
    apply frame query beyond
    rw [countNumber]
    change query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat
    exact outside
  · rw [restored,fieldsRestored]
    rfl

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_decode_fields
