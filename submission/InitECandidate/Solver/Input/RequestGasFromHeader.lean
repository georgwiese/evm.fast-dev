import InitECandidate.Solver.Input.RequestPayloadFromHeader

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- From actual full-decoder normal execution: derive the two raw fixed offsets,
safe payload extent and bounded gas expression at the real callee entry. The
later allocated payload-field store is a separate obligation. -/
theorem gas_from_header (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array cursor : BitVec 64) (heap : Blob.HeapInput source input pointer)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64)))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat)
    (cursorAligned : cursor.toNat%8=0) (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+96≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (payloadCode : source.code.lookup (ofString "decode_payload")=some (Payload.formals,Payload.body,.one))
    (enough : 12≤source.clock)
    (gas : Guest.GasLimit.declaredGasLimit input≤200000000)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source Header.body=(some (.returned value),post)) :
    Guest.GasLimit.le32 input 2=16 ∧ Guest.GasLimit.le32 input 18=44 ∧ 602≤input.length%2^64 ∧
      ∃ entry bodyPost returned gasWord,
        Blob.HeapInput entry input pointer ∧
        entry.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) ∧
        entry.code=source.code ∧ entry.eshapes=source.eshapes ∧ entry.memaddrs=source.memaddrs ∧
        entry.globals=source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 96#64))) ∧
        source.clock-11≤entry.clock ∧ evaluateHOLFiniteState entry Payload.afterGuard=(some (.returned returned),bodyPost) ∧
        eval entry Scalar.gasExpression=some (.val (.word gasWord)) ∧ gasWord.toNat≤200000000 := by
  obtain ⟨first,second,extent,minimum,sliceUpper,entry,bodyPost,returned,entryHeap,p,n,entryCode,entryShapes,entryDomain,entryGlobals,entryClock,tailRun⟩:=
    payload_from_header source post input pointer array cursor heap pointerLocal lengthLocal arrayGlobal domain pointerAligned arrayAligned upper arrayLower
      arrayBefore cursorAligned cursorAfter cursorRoom heapGlobal allocCode code failCode exceptionShape payloadCode enough value run
  obtain ⟨gasWord,gasRead,gasBound⟩:=Scalar.payload_gas_read entry input pointer entryHeap (by omega) p first second gas
  exact ⟨first,second,extent,entry,bodyPost,returned,gasWord,entryHeap,p,entryCode,entryShapes,entryDomain,entryGlobals,entryClock,tailRun,gasRead,gasBound⟩

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.gas_from_header
