import InitECandidate.Solver.Input.PayloadExtraGuard

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Normal payload execution derives its fixed and extra-data bounds through
all actual allocated stores, offset validation and rejection guards so far. -/
theorem prefix_through_extra (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length : BitVec 64) (heap : Blob.HeapInput source input pointer) (inside : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (array : BitVec 64)
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (arrayAligned : array.toNat%8=0) (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat)
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 8≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterGuard=(some (.returned value),post)) :
    Guest.GasLimit.le32 input 498=540 ∧ Guest.GasLimit.le32 input 566-540≤32 ∧
    (∀ position<4,Offsets.ValidAt 540#64 length (offsetWords input) position) ∧
      ∃ next bodyPost paid,paid≤6 ∧
        next={offsetsStored (prepared source input pointer cursor length) input array with clock:=source.clock-1-paid} ∧
        Blob.HeapInput next input pointer ∧ source.clock-7≤next.clock ∧
        evaluateHOLFiniteState next afterExtra=(some (.returned value),bodyPost) := by
  obtain ⟨raw,valid,next,bodyPost,paid,bound,nextEq,nextHeap,nextClock,nextRun⟩:=prefix_to_guard source post input pointer cursor length heap inside p n domain pointerAligned cursorAligned
    pointerLower cursorAfter cursorRoom heapGlobal allocCode array arrayGlobal arrayAligned arrayLower arrayBefore code failCode exceptionShape (by omega) value run
  have extraFirst : offsetWords input 0=540#64 := by simp [offsetWords,raw]
  have localsEq : next.locals=(prepared source input pointer cursor length).locals := by rw [nextEq]; rfl
  have fields:=declared_offsets (headerStored source pointer cursor length) input
  have extraLocal : next.locals.lookup (ofString "o_extra")=some (.val (.word 540#64)) := by
    rw [localsEq]
    change (declaredState (headerStored source pointer cursor length) input).locals.lookup (ofString "o_extra")=some (.val (.word 540#64))
    rw [←extraFirst]
    exact fields.1
  have txLocal : next.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))) := by
    rw [localsEq]
    exact fields.2.1
  have nextCode : next.code=source.code := by rw [nextEq]; rfl
  have nextShapes : next.eshapes=source.eshapes := by rw [nextEq]; rfl
  obtain ⟨short,tailRun⟩:=extra_normal next bodyPost input extraLocal txLocal (valid 1 (by decide)).1
    (by rw [nextCode]; exact failCode) (by rw [nextShapes]; exact exceptionShape) (by omega) value nextRun
  change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)).toNat-540≤32 at short
  rw [Request.le32_number input 566 (by decide)] at short
  exact ⟨raw,short,valid,next,bodyPost,paid,bound,nextEq,nextHeap,nextClock,tailRun⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.prefix_through_extra
