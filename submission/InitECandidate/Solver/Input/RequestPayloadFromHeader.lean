import InitECandidate.Solver.Input.RequestPayloadEntry

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- From a normal return of the complete fixed decoder, derive both fixed
container offsets and an actual safe payload-callee entry with copied bytes. -/
theorem payload_from_header (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source Header.body=(some (.returned value),post)) :
    Guest.GasLimit.le32 input 2=16 ∧ Guest.GasLimit.le32 input 18=44 ∧ 602≤input.length%2^64 ∧
    540≤Guest.GasLimit.le32 input 22-44 ∧ Guest.GasLimit.le32 input 22-44≤input.length%2^64-62 ∧
      ∃ entry bodyPost returned,
        Blob.HeapInput entry input pointer ∧
        entry.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) ∧
        entry.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44)))) ∧
        entry.code=source.code ∧ entry.eshapes=source.eshapes ∧ entry.memaddrs=source.memaddrs ∧
        entry.globals=source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 96#64))) ∧
        source.clock-11≤entry.clock ∧ evaluateHOLFiniteState entry Payload.afterGuard=(some (.returned returned),bodyPost) := by
  classical
  obtain ⟨first,extent,ready,innerPost,metadata,readyHeap,np,nlen,requestLower,requestUpper,requestRun⟩:=from_header source post input pointer array cursor
    heap pointerLocal lengthLocal arrayGlobal domain pointerAligned arrayAligned upper arrayLower arrayBefore cursorAligned cursorAfter cursorRoom
    heapGlobal allocCode code failCode exceptionShape (by omega) value run
  have readyArray : ready.globals.lookup (ofString "ssz_offs")=some (.val (.word array)) := by
    rw [metadata.globals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "heap_ptr"==ofString "ssz_offs")=false from by decide,if_false] using arrayGlobal
  have totalNumber : (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6-16)).toNat=Guest.GasLimit.le32 input 6-16 := by
    have small : input.length%2^64<2^64 := Nat.mod_lt _ (by decide)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨second,safeExtent,minimum,sliceUpper,entry,bodyPost,returned,entryHeap,p,n,entryCode,entryShapes,entryDomain,entryGlobals,entryClock,tailRun⟩:=
    payload_reachable ready innerPost input pointer array (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6-16)) readyHeap extent np nlen readyArray
      (metadata.domain.trans domain) pointerAligned arrayAligned upper arrayLower arrayBefore
      (by rw [metadata.code]; exact code) (by rw [metadata.code]; exact failCode) (by rw [metadata.exceptions]; exact exceptionShape)
      (by rw [metadata.code]; exact payloadCode) (by rw [totalNumber]; exact requestUpper) (by have h:=metadata.clockLower; omega) value requestRun
  refine ⟨first,second,safeExtent,minimum,sliceUpper,entry,bodyPost,returned,entryHeap,p,n,
    entryCode.trans metadata.code,entryShapes.trans metadata.exceptions,entryDomain.trans metadata.domain,
    entryGlobals.trans metadata.globals,?_,tailRun⟩
  have readyClock:=metadata.clockLower
  omega

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.payload_from_header
