import InitECandidate.Solver.Input.PayloadAllocatedNormal
import InitECandidate.Solver.Input.PayloadAfterExtraImage
import InitECandidate.Solver.Input.PayloadPreparedImage
import InitECandidate.Solver.Input.PayloadImageCells
import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual original allocated payload returns all seventeen physical
fields and its real transaction records, with the entire readonly context
(including FFI) retained. Only eight prefix ticks are assumed here. -/
theorem allocated_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (enough : 8≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterGuard=(some (.returned value),post)) :
    Image post input pointer cursor length (PersistentAlloc.rounded cursor 136#64) ∧
      VarList.Records post input pointer (PersistentAlloc.rounded cursor 136#64) (62+Guest.GasLimit.le32 input 566) (transactionBytes input) ∧
      InitializerAllocations.context post=InitializerAllocations.context source := by
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
  obtain ⟨valueEq,matching,records,control⟩ := after_extra_image next innerPost input pointer cursor (PersistentAlloc.rounded cursor 136#64) length nextHeap extent
    (by rw [localsEq]; exact fields.1) (by rw [localsEq]; exact fields.2.1) (by rw [localsEq]; exact fields.2.2)
    (by rw [localsEq,←extraEq]; exact offsets.1) (by rw [localsEq]; exact offsets.2.1)
    (by rw [localsEq]; exact offsets.2.2.1) (by rw [localsEq]; exact offsets.2.2.2)
    valid inside (domainEq.trans domain) pointerAligned cursorAligned newAligned pointerLower cursorAfter (by omega) newAfter (by omega)
    (by rw [arrayNumber]) nextHeapGlobal (by rw [codeEq]; exact allocCode) (by rw [codeEq]; exact divisionCode) (by rw [codeEq]; exact failCode)
    (by rw [shapesEq]; exact exceptionShape) (by rw [codeEq]; exact varCode) (by rw [codeEq]; exact fixedCode) value nextRun
  have headers := prepared_header_cells source input pointer cursor length array (by omega) (by omega)
  have nextPointer : next.memory cursor=.word (pointer+62#64) := by rw [nextEq]; exact headers.1
  have nextLength : next.memory (cursor+8#64)=.word length := by rw [nextEq]; exact headers.2
  have canonical := image_after_fields next input pointer cursor length (PersistentAlloc.rounded cursor 136#64) (by omega) nextPointer nextLength
  have image : Image innerPost input pointer cursor length (PersistentAlloc.rounded cursor 136#64) := by
    intro field member
    have bound := (image_fields_valid input pointer length (PersistentAlloc.rounded cursor 136#64) field member).1
    have number : (cursor+BitVec.ofNat 64 field.1).toNat=cursor.toNat+field.1 := WitnessRadix.byteAddress_toNat cursor field.1 (by omega)
    rw [matching _ (by rw [number,arrayNumber]; omega)]
    exact canonical field member
  have innerContext : InitializerAllocations.context innerPost=InitializerAllocations.context next := by
    by_cases empty : transactionBytes input=0
    · simp only [if_pos empty] at control
      have h := congrArg InitializerAllocations.context control
      exact h
    · simp only [if_neg empty] at control
      have h := congrArg InitializerAllocations.context control
      exact h
  have nextContext : InitializerAllocations.context next=InitializerAllocations.context source := by rw [nextEq]; rfl
  have finalMemory : post.memory=innerPost.memory := by rw [postEq]; rfl
  refine ⟨Image.of_memory innerPost post input pointer cursor length (PersistentAlloc.rounded cursor 136#64) finalMemory image,
    VarList.Records.of_memory innerPost post input pointer (PersistentAlloc.rounded cursor 136#64) _ _ finalMemory records,?_⟩
  rw [postEq]
  exact innerContext.trans nextContext

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.allocated_image
