import InitECandidate.Solver.Input.PayloadBodyNormal

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal full fixed input decoder reaches an actual completed allocated
payload whose gas field obeys the challenge gas bound. The SI and payload
allocation cursors and room are derived through their real updates. -/
theorem stored_gas_from_header (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array cursor : BitVec 64) (heap : Blob.HeapInput source input pointer)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64)))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAligned : cursor.toNat%8=0) (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+232+4*(input.length%2^64)≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (offsetCode : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (fixedCode : source.code.lookup (ofString "ssz_fixed_list_count")=some (FixedList.formals,FixedList.body,.one))
    (payloadCode : source.code.lookup (ofString "decode_payload")=some (Payload.formals,Payload.body,.one))
    (enough : (input.length%2^64)/4+87≤source.clock)
    (gas : Guest.GasLimit.declaredGasLimit input≤200000000)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source Header.body=(some (.returned value),post)) :
    Guest.GasLimit.le32 input 2=16 ∧ Guest.GasLimit.le32 input 18=44 ∧
      ∃ entry payloadPost gasWord,
        let payloadCursor:=WitnessRadix.PersistentAlloc.rounded cursor 96#64
        evaluateHOLFiniteState entry Payload.afterGuard=(some (.returned (.val (.word payloadCursor))),payloadPost) ∧
        payloadPost.memory (payloadCursor+88#64)=.word gasWord ∧ gasWord.toNat≤200000000 ∧
        Blob.HeapInput payloadPost input pointer ∧
        source.clock-((input.length%2^64)/4+86)≤payloadPost.clock := by
  classical
  obtain ⟨first,second,extent,minimum,sliceUpper,entry,payloadPost,returned,entryHeap,p,n,entryCode,entryShapes,entryDomain,entryGlobals,entryClock,tailRun⟩:=
    payload_from_header source post input pointer array cursor heap pointerLocal lengthLocal arrayGlobal domain pointerAligned arrayAligned (by omega)
      arrayLower arrayBefore cursorAligned cursorAfter (by omega) heapGlobal allocCode offsetCode failCode exceptionShape payloadCode (by omega) value run
  let payloadCursor:=WitnessRadix.PersistentAlloc.rounded cursor 96#64
  have roundedNumber:=WitnessRadix.PersistentAlloc.rounded_nat cursor 96#64 (by change cursor.toNat+96+7<2^64; omega)
  change payloadCursor.toNat=(cursor.toNat+96+7)/8*8 at roundedNumber
  have payloadNumber : payloadCursor.toNat=cursor.toNat+96 := by omega
  have lengthNumber : (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44)).toNat=Guest.GasLimit.le32 input 22-44 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=RawScalar.le32_lt input 22; omega)]
  have entryArray : entry.globals.lookup (ofString "ssz_offs")=some (.val (.word array)) := by
    rw [entryGlobals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "heap_ptr"==ofString "ssz_offs")=false from by decide] using arrayGlobal
  have entryHeapGlobal : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word payloadCursor)) := by
    rw [entryGlobals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,payloadCursor]
  obtain ⟨returnedEq,gasCell,finalHeap,clockLower,clockUpper,countCell,heapCursor,countBound⟩:=Payload.allocated_normal entry payloadPost input pointer payloadCursor
    (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44)) entryHeap extent p n (by rw [lengthNumber]; omega)
    (entryDomain.trans domain) pointerAligned (by omega) pointerLower (by omega) (by omega) entryHeapGlobal
    (by rw [entryCode]; exact allocCode) array entryArray arrayAligned arrayLower arrayBefore
    (by rw [entryCode]; exact offsetCode) (by rw [entryCode]; exact divisionCode) (by rw [entryCode]; exact failCode)
    (by rw [entryShapes]; exact exceptionShape) (by rw [entryCode]; exact varCode) (by rw [entryCode]; exact fixedCode)
    (by omega) returned tailRun
  refine ⟨first,second,entry,payloadPost,BitVec.ofNat 64 (Guest.GasLimit.le64 input 474),?_,gasCell,
    Payload.stored_gas_bound input first second gas,finalHeap,by omega⟩
  simpa only [returnedEq] using tailRun

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.stored_gas_from_header
