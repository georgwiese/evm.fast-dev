import InitECandidate.Solver.Input.PayloadAfterExtraNormal
import InitECandidate.Solver.Input.PayloadPreparedFacts

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Entire actual allocated payload decoder, with all guards, list calls,
stores and lexical restorations. On normal return, field88 is the real input
gas word. No validity assumption is imposed on either decoded list. -/
theorem allocated_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length : BitVec 64) (heap : Blob.HeapInput source input pointer) (extent : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (inside : 62+length.toNat≤input.length%2^64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136+4*(input.length%2^64)≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (array : BitVec 64) (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (arrayAligned : array.toNat%8=0) (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat)
    (offsetCode : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (fixedCode : source.code.lookup (ofString "ssz_fixed_list_count")=some (FixedList.formals,FixedList.body,.one))
    (enough : (input.length%2^64)/4+76≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterGuard=(some (.returned value),post)) :
    value=.val (.word cursor) ∧ post.memory (cursor+88#64)=.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      Blob.HeapInput post input pointer ∧ source.clock-((input.length%2^64)/4+75)≤post.clock ∧ post.clock≤source.clock ∧ post.memory (cursor+56#64)=.word (BitVec.ofNat 64 (withdrawalCount input)) := by
  classical
  obtain ⟨first,extraBound,valid,next,innerPost,paid,bound,nextEq,nextHeap,clockLower,nextRun,postEq⟩:=prefix_through_extra source post input pointer cursor length
    heap extent p n domain pointerAligned cursorAligned pointerLower cursorAfter (by omega) heapGlobal allocCode array arrayGlobal
    arrayAligned arrayLower arrayBefore offsetCode failCode exceptionShape (by omega) value run
  have localsEq : next.locals=(prepared source input pointer cursor length).locals := by rw [nextEq]; rfl
  have codeEq : next.code=source.code := by rw [nextEq]; rfl
  have shapesEq : next.eshapes=source.eshapes := by rw [nextEq]; rfl
  have domainEq : next.memaddrs=source.memaddrs := by rw [nextEq]; rfl
  have nextClock : next.clock=source.clock-1-paid := by rw [nextEq]
  have fields:=prepared_locals source input pointer cursor length p n
  have offsets:=declared_offsets (headerStored source pointer cursor length) input
  have extraEq : offsetWords input 0=540#64 := by simp [offsetWords,first]
  obtain ⟨orderedLower,ordered,contained⟩:=transaction_range input length valid inside
  have transactionLength : Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566≤input.length%2^64 := by omega
  obtain ⟨arrayNumber,newAligned,newAfter,newRoom⟩:=payload_array_geometry input pointer cursor cursorAligned cursorAfter cursorRoom
  have nextHeapGlobal : next.globals.lookup (ofString "heap_ptr")=some (.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 136#64))) := by
    rw [nextEq]
    exact prepared_heap source input pointer cursor length
  obtain ⟨valueEq,gasCell,finalHeap,finalLower,finalUpper,countCell⟩:=after_extra_normal next innerPost input pointer cursor
    (WitnessRadix.PersistentAlloc.rounded cursor 136#64) length nextHeap extent
    (by rw [localsEq]; exact fields.1) (by rw [localsEq]; exact fields.2.1) (by rw [localsEq]; exact fields.2.2)
    (by rw [localsEq,←extraEq]; exact offsets.1) (by rw [localsEq]; exact offsets.2.1)
    (by rw [localsEq]; exact offsets.2.2.1) (by rw [localsEq]; exact offsets.2.2.2)
    valid inside (domainEq.trans domain) pointerAligned cursorAligned newAligned pointerLower cursorAfter (by omega) newAfter (by omega)
    nextHeapGlobal (by rw [codeEq]; exact allocCode) (by rw [codeEq]; exact divisionCode) (by rw [codeEq]; exact failCode)
    (by rw [shapesEq]; exact exceptionShape) (by rw [codeEq]; exact varCode) (by rw [codeEq]; exact fixedCode) (by omega) value nextRun
  have postClock : post.clock=innerPost.clock := by rw [postEq]; rfl
  refine ⟨valueEq,?_,?_,?_,?_,?_⟩
  · rw [postEq]; exact gasCell
  · rw [postEq]
    exact Blob.HeapInput.of_fields innerPost (restorePrefix source input pointer cursor length innerPost) input pointer rfl rfl rfl finalHeap
  · omega
  · omega
  · rw [postEq]
    exact countCell

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.allocated_normal
