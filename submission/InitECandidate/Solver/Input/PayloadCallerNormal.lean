import InitECandidate.Solver.Input.PayloadBodyNormal
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual complete payload call resumption, carrying the allocated pointer,
its real gas field, copied input, bounded clocks and invariant code fields. -/
theorem caller_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length : BitVec 64) (heap : Blob.HeapInput source input pointer)
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
    (payloadCode : source.code.lookup (ofString "decode_payload")=some (formals,body,.one))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (values (pointer+62#64) length))
    (enough : (input.length%2^64)/4+77≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "decode_payload") expressions continuation)=(some (.returned value),post)) :
    ∃ next innerPost,next.locals=source.locals.update (ofString name,.val (.word cursor)) ∧
      Blob.HeapInput next input pointer ∧ next.memory (cursor+88#64)=.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      source.clock-((input.length%2^64)/4+76)≤next.clock ∧ next.clock≤source.clock ∧
      next.code=source.code ∧ next.memaddrs=source.memaddrs ∧ next.eshapes=source.eshapes ∧
      evaluateHOLFiniteState next continuation=(some (.returned value),innerPost) ∧ post=restore source name innerPost ∧ next.memory (cursor+56#64)=.word (BitVec.ofNat 64 (withdrawalCount input)) := by
  classical
  obtain ⟨callee,called,p,n⟩:=environment source.code.lookup (pointer+62#64) length payloadCode
  obtain ⟨bodyPost,returned,bodyRun⟩:=CallNormal.callee_return source post (ofString name) .one (ofString "decode_payload") expressions
    (values (pointer+62#64) length) body continuation callee .one args called (by omega) value run
  let entry:=callEntryStateHOLFinite source callee
  have entryHeap : Blob.HeapInput entry input pointer:=Blob.HeapInput.of_fields source entry input pointer rfl rfl rfl heap
  obtain ⟨valueEq,gasCell,bodyHeap,bodyLower,bodyUpper,countCell⟩:=body_normal entry bodyPost input pointer cursor length entryHeap p n inside domain
    pointerAligned cursorAligned pointerLower cursorAfter cursorRoom heapGlobal allocCode array arrayGlobal arrayAligned arrayLower arrayBefore
    offsetCode divisionCode failCode exceptionShape varCode fixedCode (by change (input.length%2^64)/4+76≤source.clock-1; omega) returned bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one)=true := by
    rw [valueEq]
    simp [shapeOfHOLExact,shapeEqHOL]
  have actual:=CallNormal.return_execute source bodyPost name .one (ofString "decode_payload") expressions (values (pointer+62#64) length)
    body continuation callee .one returned args called (by omega) bodyRun shapePass
  have normal:=actual.symm.trans run
  let next:=CallNormal.continuationEntry source bodyPost name returned
  have result : (evaluateHOLFiniteState next continuation).1=some (.returned value):=congrArg Prod.fst normal
  have postEq : post=restore source name (evaluateHOLFiniteState next continuation).2:=(congrArg Prod.snd normal).symm
  have fields:=evaluation_fields entry bodyPost body (some (.returned returned)) bodyRun
  refine ⟨next,(evaluateHOLFiniteState next continuation).2,?_,?_,gasCell,?_,?_,fields.2.2.2,fields.1,fields.2.2.1,Prod.ext result rfl,postEq,countCell⟩
  · change source.locals.update (ofString name,returned)=source.locals.update (ofString name,.val (.word cursor))
    rw [valueEq]
  · exact Blob.HeapInput.of_fields bodyPost next input pointer rfl rfl rfl bodyHeap
  · change source.clock-((input.length%2^64)/4+76)≤bodyPost.clock
    change source.clock-1-((input.length%2^64)/4+75)≤bodyPost.clock at bodyLower
    omega
  · change bodyPost.clock≤source.clock
    change bodyPost.clock≤source.clock-1 at bodyUpper
    omega

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.caller_normal
