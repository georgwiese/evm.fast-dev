import InitECandidate.Solver.Input.PayloadAfterExtraNormal
import InitECandidate.Solver.Input.PayloadTailTrace
import InitECandidate.Solver.Input.VarList.CallerTrace

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual payload transaction and withdrawal lists on every non-timeout
path, including malformed transaction headers/records and withdrawal counts.
All remaining stores/return execute in the actual reached continuation. -/
theorem after_extra_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (fixedCode : source.code.lookup (ofString "ssz_fixed_list_count")=some (FixedList.formals,FixedList.body,.one))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterExtra=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)/4+69 ∧
      ((∃ error : BitVec 64,(error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=30#64 ∨ error=31#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨ result=some (.returned (.val (.word cursor)))) := by
  obtain ⟨lower,ordered,contained⟩ := transaction_range input length valid inside
  obtain ⟨prefixRun,prefixHeap⟩ := extra_stores source input pointer cursor heap p pl e t lower domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
  let stored := extraStoredPayload source input pointer cursor
  have storedClock : stored.clock=source.clock := rfl
  have tailRun : evaluateHOLFiniteState stored transactionCall=(result,post) := prefixRun.symm.trans run
  have args := transaction_arguments stored input pointer p t w ordered contained
  rw [transactions_shape.2.1] at tailRun
  rcases VarList.caller_trace stored post input pointer array 9223372036854775807#64 (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)
    prefixHeap args.2 domain pointerLower pointerAligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape "txs" transactionArguments afterTransactions args.1 varCode result tailRun notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    rw [storedClock] at cost
    exact ⟨by omega,Or.inl ⟨error,by rcases allowed with rfl | rfl | rfl | rfl <;> simp,same⟩⟩
  obtain ⟨next,innerPost,localsEq,control,nextHeap,oldMemory,records,countLimit,forward,cost,nextRun,postEq⟩ := normal
  let recordArray := VarList.decodedArray array (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)
  let count := BitVec.ofNat 64 (VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566))
  have txs : next.locals.lookup (ofString "txs")=some (UDivMod.pairValue recordArray count) := by
    rw [localsEq]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,UDivMod.pairValue,VarList.pairValue,recordArray,count]
  have storedLocals : stored.locals=source.locals := rfl
  have localOther (name : String) (different : ofString "txs"≠ofString name) : next.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    rw [localsEq]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,different,storedLocals]
  obtain ⟨domains,codes,shapes⟩ := allocation_control_fields stored next array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input (62+Guest.GasLimit.le32 input 566)/4)))
    (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566=0) control
  obtain ⟨tailCost,outcome⟩ := after_transactions_trace next innerPost input pointer cursor length recordArray count (offsetWords input 2) (offsetWords input 3) nextHeap extent
    ((localOther "p" (by decide)).trans p) ((localOther "pl" (by decide)).trans pl) ((localOther "len" (by decide)).trans n) txs
    ((localOther "o_wd" (by decide)).trans w) ((localOther "o_bal" (by decide)).trans b) (domains.trans domain) pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
    (by rw [codes]; exact divisionCode) (by rw [codes]; exact failCode) (by rw [shapes]; exact exceptionShape) (by rw [codes]; exact fixedCode) result nextRun notTimeout
  have tailForward := evaluateHOLFiniteState_clock_le next afterTransactions
  rw [nextRun] at tailForward
  change innerPost.clock≤next.clock at tailForward
  have clock : post.clock=innerPost.clock := by rw [postEq]; rfl
  change next.clock≤source.clock at forward
  change source.clock-next.clock≤(Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)/4+2 at cost
  refine ⟨by rw [clock]; omega,?_⟩
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    exact Or.inl ⟨error,Or.inr (Or.inr (Or.inr (Or.inr allowed))),same⟩
  · exact Or.inr normal

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.after_extra_trace
