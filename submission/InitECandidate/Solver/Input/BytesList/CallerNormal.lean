import InitECandidate.Solver.Input.BytesList.Environment

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual byte-list call returns concrete initialized records, per-item size
bounds and the actual count-limit check into its saved caller continuation. -/
theorem caller_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit maximum : BitVec 64) (start length : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+length≤input.length%2^64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*length≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (code : source.code.lookup (ofString "decode_bytes_list")=some (formals,body,VarList.returnShape))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum))
    (enough : 2*(length/4)+5≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) VarList.returnShape (ofString "decode_bytes_list") expressions continuation)=(some (.returned value),post)) :
    ∃ next innerPost,next.locals=source.locals.update (ofString name,pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length)) ∧
      VarList.Records next input pointer array start length ∧ VarList.decodedCount input start length≤limit.toNat ∧ Blob.HeapInput next input pointer ∧
      (∀ position<VarList.decodedCount input start length,
        (VarList.recordLength input start length (VarList.decodedCount input start length) position).toNat≤maximum.toNat) ∧
      source.clock-(2*(length/4)+3)≤next.clock ∧ next.clock≤source.clock ∧
      (∀ query : BitVec 64,query.toNat<array.toNat→next.memory query=source.memory query) ∧
      next.code=source.code ∧ next.memaddrs=source.memaddrs ∧ next.eshapes=source.eshapes ∧
      evaluateHOLFiniteState next continuation=(some (.returned value),innerPost) ∧ post=restore source name innerPost := by
  classical
  obtain ⟨callee,called,p,n,l,m⟩:=environment source.code.lookup (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum code
  obtain ⟨bodyPost,returned,bodyRun⟩:=CallNormal.callee_return source post (ofString name) VarList.returnShape (ofString "decode_bytes_list") expressions
    (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum) body continuation callee VarList.returnShape args called (by omega) value run
  let entry:=callEntryStateHOLFinite source callee
  have entryHeap : Blob.HeapInput entry input pointer:=Blob.HeapInput.of_fields source entry input pointer rfl rfl rfl heap
  obtain ⟨valueEq,records,countLimit,bodyHeap,lengthBound,bodyLower,bodyUpper,oldMemory⟩:=body_normal entry bodyPost input pointer array limit maximum start length
    entryHeap inside p n l domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape varCode m
    (by change 2*(length/4)+4≤source.clock-1; omega) returned bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact returned) VarList.returnShape && shapeEqHOL (shapeOfHOLExact returned) VarList.returnShape)=true := by
    rw [valueEq]
    simp [pairValue,VarList.pairValue,VarList.returnShape,shapeOfHOLExact,shapeEqHOL_eq_true]
  have actual:=CallNormal.return_execute source bodyPost name VarList.returnShape (ofString "decode_bytes_list") expressions
    (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum) body continuation callee VarList.returnShape returned args called (by omega) bodyRun shapePass
  have normal:=actual.symm.trans run
  let next:=CallNormal.continuationEntry source bodyPost name returned
  have result : (evaluateHOLFiniteState next continuation).1=some (.returned value):=congrArg Prod.fst normal
  have postEq : post=restore source name (evaluateHOLFiniteState next continuation).2:=(congrArg Prod.snd normal).symm
  have fields:=evaluation_fields entry bodyPost body (some (.returned returned)) bodyRun
  refine ⟨next,(evaluateHOLFiniteState next continuation).2,?_,VarList.Records.of_memory bodyPost next input pointer array start length rfl records,
    countLimit,Blob.HeapInput.of_fields bodyPost next input pointer rfl rfl rfl bodyHeap,lengthBound,?_,?_,oldMemory,
    fields.2.2.2,fields.1,fields.2.2.1,Prod.ext result rfl,postEq⟩
  · change source.locals.update (ofString name,returned)=_
    rw [valueEq]
  · change source.clock-(2*(length/4)+3)≤bodyPost.clock
    change source.clock-1-(2*(length/4)+2)≤bodyPost.clock at bodyLower
    omega
  · change bodyPost.clock≤source.clock
    change bodyPost.clock≤source.clock-1 at bodyUpper
    omega

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.caller_normal
