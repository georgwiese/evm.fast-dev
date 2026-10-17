import InitECandidate.Solver.Input.PayloadPrefixNormal

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole real payload allocation/header/declarations/stores/validator prefix.
Normal execution derives the fixed extra-data offset540, with at most seven
source clocks and copied-input preservation. -/
theorem prefix_to_guard (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 7≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterGuard=(some (.returned value),post)) :
    Guest.GasLimit.le32 input 498=540 ∧ (∀ position<4,Offsets.ValidAt 540#64 length (offsetWords input) position) ∧
      ∃ next bodyPost paid,paid≤6 ∧
        next={offsetsStored (prepared source input pointer cursor length) input array with clock:=source.clock-1-paid} ∧
        Blob.HeapInput next input pointer ∧ source.clock-7≤next.clock ∧
        evaluateHOLFiniteState next offsetContinuation=(some (.returned value),bodyPost) ∧ post=restorePrefix source input pointer cursor length bodyPost := by
  classical
  obtain ⟨setup,readyHeap⟩:=prefix_setup source input pointer cursor length heap inside p n domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom heapGlobal allocCode (by omega)
  obtain ⟨innerPost,readyRun,postEq⟩:=prefix_normal source post input pointer cursor length (restorePrefix source input pointer cursor length) setup value run
  let ready:=prepared source input pointer cursor length
  have readyGlobals : ready.globals=source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 136#64))) := rfl
  have readyArray : ready.globals.lookup (ofString "ssz_offs")=some (.val (.word array)) := by
    rw [readyGlobals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "heap_ptr"==ofString "ssz_offs")=false from by decide] using arrayGlobal
  obtain ⟨l0,l1,l2,l3⟩:=declared_offsets (headerStored source pointer cursor length) input
  have headerN : (headerStored source pointer cursor length).locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} cursor 136#64) "pl" "len" cursor (by decide)).trans n
  have readyN : ready.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (declared_other (headerStored source pointer cursor length) input "len" (by decide) (by decide) (by decide) (by decide)).trans headerN
  obtain ⟨first,valid,next,paid,bound,nextEq,nextHeap,nextRun⟩:=offsets_normal ready innerPost input pointer array length readyHeap readyArray l0 l1 l2 l3
    domain pointerAligned arrayAligned (by omega) arrayLower arrayBefore readyN code failCode exceptionShape (by change 6≤source.clock-1; omega) value readyRun
  have raw:=congrArg BitVec.toNat first
  change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 498)).toNat=540 at raw
  rw [Request.le32_number input 498 (by decide)] at raw
  have readyClock : ready.clock=source.clock-1 := rfl
  have nextClock:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.clock) nextEq
  change next.clock=ready.clock-paid at nextClock
  rw [readyClock] at nextClock nextEq
  refine ⟨raw,valid,next,innerPost,paid,bound,nextEq,nextHeap,?_,nextRun,postEq⟩
  rw [nextClock]
  omega

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.prefix_to_guard
