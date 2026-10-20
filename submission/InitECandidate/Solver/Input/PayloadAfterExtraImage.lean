import InitECandidate.Solver.Input.PayloadAfterExtraTrace
import InitECandidate.Solver.Input.PayloadImage
import InitECandidate.Solver.Input.StructureFieldFrame
import InitECandidate.Solver.Input.VarList.RecordsAfterFrame

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Physical result of the actual original transaction/withdrawal suffix.
Every payload word below the real transaction array matches its actual
constant writes; transaction records survive all later field writes, and the
complete original nonlocal control/FFI state is retained. -/
theorem after_extra_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor array length : BitVec 64) (heap : Blob.HeapInput source input pointer) (extent : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (e : source.locals.lookup (ofString "o_extra")=some (.val (.word 540#64)))
    (t : source.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))))
    (w : source.locals.lookup (ofString "o_wd")=some (.val (.word (offsetWords input 2))))
    (b : source.locals.lookup (ofString "o_bal")=some (.val (.word (offsetWords input 3))))
    (valid : ∀ position<4,Offsets.ValidAt 540#64 length (offsetWords input) position)
    (inside : 62+length.toNat≤input.length%2^64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*(Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)≤33806089496)
    (beforeArray : cursor.toNat+136≤array.toNat)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (fixedCode : source.code.lookup (ofString "ssz_fixed_list_count")=some (FixedList.formals,FixedList.body,.one))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterExtra=(some (.returned value),post)) :
    value=.val (.word cursor) ∧
      (∀ query,query.toNat<array.toNat → post.memory query=(applyFields source cursor (afterExtraFields input pointer length array)).memory query) ∧
      VarList.Records post input pointer array (62+Guest.GasLimit.le32 input 566) (transactionBytes input) ∧
      WitnessRadix.BackingLayout.control post=WitnessRadix.BackingLayout.control
        (if transactionBytes input=0 then source else PersistentAlloc.post source array (BitVec.ofNat 64 (16*transactionCount input))) := by
  obtain ⟨txLower,txOrdered,txInside⟩ := transaction_range input length valid inside
  obtain ⟨prefixRun,prefixHeap⟩ := extra_stores source input pointer cursor heap p pl e t txLower domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
  let stored := extraStoredPayload source input pointer cursor
  have tailRun : evaluateHOLFiniteState stored transactionCall=(some (.returned value),post) := prefixRun.symm.trans run
  have args := transaction_arguments stored input pointer p t w txOrdered txInside
  rw [transactions_shape.2.1] at tailRun
  rcases VarList.caller_trace stored post input pointer array 9223372036854775807#64 (62+Guest.GasLimit.le32 input 566) (transactionBytes input)
    prefixHeap args.2 domain pointerLower pointerAligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape "txs" transactionArguments afterTransactions args.1 varCode (some (.returned value)) tailRun (by simp) with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    cases same
  obtain ⟨next,innerPost,localsEq,control,nextHeap,oldMemory,records,countLimit,forward,cost,nextRun,postEq⟩ := normal
  let recordArray := VarList.decodedArray array (transactionBytes input)
  let count := BitVec.ofNat 64 (transactionCount input)
  have txs : next.locals.lookup (ofString "txs")=some (UDivMod.pairValue recordArray count) := by
    rw [localsEq]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,UDivMod.pairValue,VarList.pairValue,recordArray,count,transactionCount]
  have storedLocals : stored.locals=source.locals := rfl
  have localOther (name : String) (different : ofString "txs"≠ofString name) : next.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    rw [localsEq]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,different,storedLocals]
  obtain ⟨domains,codes,shapes⟩ := allocation_control_fields stored next array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input (62+Guest.GasLimit.le32 input 566)/4))) (transactionBytes input=0) control
  obtain ⟨tailCost,outcome⟩ := after_transactions_trace_image next innerPost input pointer cursor length recordArray count (offsetWords input 2) (offsetWords input 3) nextHeap extent
    ((localOther "p" (by decide)).trans p) ((localOther "pl" (by decide)).trans pl) ((localOther "len" (by decide)).trans n) txs
    ((localOther "o_wd" (by decide)).trans w) ((localOther "o_bal" (by decide)).trans b) (domains.trans domain) pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
    (by rw [codes]; exact divisionCode) (by rw [codes]; exact failCode) (by rw [shapes]; exact exceptionShape) (by rw [codes]; exact fixedCode) (some (.returned value)) nextRun (by simp)
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    cases same
  obtain ⟨same,wdCount,wdNumber,wdRemainder,tailMemory,tailControl⟩ := normal
  have valueEq : value=.val (.word cursor) := by cases same; rfl
  have wdNat : wdCount.toNat=withdrawalCount input := by rw [wdNumber,(withdrawal_difference input length valid).2.1]; rfl
  have wdEq : wdCount=BitVec.ofNat 64 (withdrawalCount input) := BitVec.eq_of_toNat_eq (wdNat.trans (withdrawal_count_number input).symm)
  rw [wdEq] at tailMemory
  let tailFields : List Field :=
    [(32,.rfield 0 (localVar "txs"),recordArray),(40,.rfield 1 (localVar "txs"),count)] ++
      remainingFields input pointer length (offsetWords input 2) (offsetWords input 3) (BitVec.ofNat 64 (withdrawalCount input))
  have postMemory : post.memory=innerPost.memory := by rw [postEq]; rfl
  have exactMemory : post.memory=fieldMemory next.memory cursor tailFields := by
    rw [postMemory,tailMemory]
    rfl
  have matching (query : BitVec 64) (before : query.toNat<array.toNat) : post.memory query=(applyFields source cursor (afterExtraFields input pointer length array)).memory query := by
    rw [exactMemory]
    change fieldMemory next.memory cursor tailFields query=fieldMemory stored.memory cursor tailFields query
    exact fieldMemory_point next.memory stored.memory cursor query tailFields (oldMemory query before)
  have tailValid : ∀ field∈tailFields,field.1<136 := by
    intro field member
    simp only [tailFields,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (rfl | rfl) | member
    · simp only [Prod.fst]; decide
    · simp only [Prod.fst]; decide
    · have bound := (remaining_valid input pointer length (offsetWords input 2) (offsetWords input 3) (BitVec.ofNat 64 (withdrawalCount input)) field member).1
      omega
  have postRecords : VarList.Records post input pointer array (62+Guest.GasLimit.le32 input 566) (transactionBytes input) := by
    apply VarList.Records.of_after next post input pointer array _ _ (cursor.toNat+136) records beforeArray
    intro query after
    rw [exactMemory]
    exact StructureStore.apply_fields_outside next cursor 136 ⟨by omega,cursorRoom⟩ tailFields tailValid query (Or.inr after)
  have postControl : BackingLayout.control post=BackingLayout.control next := by rw [postEq]; exact tailControl
  have fullControl : BackingLayout.control post=BackingLayout.control
      (if transactionBytes input=0 then source else PersistentAlloc.post source array (BitVec.ofNat 64 (16*transactionCount input))) := by
    by_cases empty : transactionBytes input=0
    · simp only [if_pos empty] at control ⊢
      exact postControl.trans control
    · simp only [if_neg empty] at control ⊢
      have countNat : transactionCount input=Guest.GasLimit.le32 input (62+Guest.GasLimit.le32 input 566)/4 := by simp [transactionCount,VarList.decodedCount,empty]
      rw [countNat]
      exact postControl.trans control
  exact ⟨valueEq,matching,postRecords,fullControl⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.after_extra_image
