import InitECandidate.Solver.Input.BytesList.BodyTrace
import InitECandidate.Solver.Input.BytesList.Environment
import InitECandidate.Solver.Input.NonTimeoutScopedCall

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Real byte-list scoped call, including every parser/size failure, or its
actual tuple and records at the unchanged arbitrary continuation. -/
theorem caller_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) VarList.returnShape (ofString "decode_bytes_list") expressions continuation)=(result,post)) (notTimeout : result≠some .timeOut) :
    (∃ error : BitVec 64,(error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock-post.clock≤2*(length/4)+4) ∨
    (∃ next innerPost,next.locals=source.locals.update (ofString name,pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length)) ∧
      VarList.Records next input pointer array start length ∧ VarList.decodedCount input start length≤limit.toNat ∧ Blob.HeapInput next input pointer ∧
      (∀ position<VarList.decodedCount input start length,(VarList.recordLength input start length (VarList.decodedCount input start length) position).toNat≤maximum.toNat) ∧
      source.clock-next.clock≤2*(length/4)+4 ∧ next.clock≤source.clock ∧
      (∀ query : BitVec 64,query.toNat<array.toNat → next.memory query=source.memory query) ∧
      next.code=source.code ∧ next.memaddrs=source.memaddrs ∧ next.eshapes=source.eshapes ∧
      evaluateHOLFiniteState next continuation=(result,innerPost) ∧ post=restore source name innerPost ∧
      WitnessRadix.BackingLayout.control next=WitnessRadix.BackingLayout.control
        (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4))))) := by
  classical
  obtain ⟨callee,called,p,n,l,m⟩ := environment source.code.lookup (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum code
  obtain ⟨funded,bodyNonTimeout⟩ := scoped_call_non_timeout source post (ofString name) VarList.returnShape (ofString "decode_bytes_list") expressions
    (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum) body continuation callee VarList.returnShape args called result run notTimeout
  let entry := callEntryStateHOLFinite source callee
  let bodyResult := (evaluateHOLFiniteState entry body).1
  let bodyPost := (evaluateHOLFiniteState entry body).2
  have bodyRun : evaluateHOLFiniteState entry body=(bodyResult,bodyPost) := rfl
  have entryHeap : Blob.HeapInput entry input pointer := Blob.HeapInput.of_fields source entry input pointer rfl rfl rfl heap
  obtain ⟨bodyCost,outcome⟩ := body_trace entry bodyPost input pointer array limit maximum start length entryHeap inside p n l domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape varCode m bodyResult bodyRun bodyNonTimeout
  have forward : bodyPost.clock≤source.clock-1 := evaluateHOLFiniteState_clock_le entry body
  have cost : source.clock-bodyPost.clock≤2*(length/4)+4 := by change source.clock-1-bodyPost.clock≤2*(length/4)+3 at bodyCost; omega
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    have actualBody : evaluateHOLFiniteState entry body=(some (.exception (ofString "SszErr") (.val (.word error))),bodyPost) := Prod.ext same rfl
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
    simp only [args,called,if_neg (show source.clock≠0 by omega)] at run
    rw [actualBody] at run
    have endpoint : post.clock=bodyPost.clock := by have h := congrArg (fun output => output.2.clock) run; exact h.symm
    exact Or.inl ⟨error,allowed,(congrArg Prod.fst run).symm,by rw [endpoint]; exact cost⟩
  · obtain ⟨same,records,countLimit,bytes,sizes,memory,control⟩ := normal
    let returned := pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length)
    have actualBody : evaluateHOLFiniteState entry body=(some (.returned returned),bodyPost) := Prod.ext same rfl
    have shapePass : (shapeEqHOL (shapeOfHOLExact returned) VarList.returnShape && shapeEqHOL (shapeOfHOLExact returned) VarList.returnShape)=true := by
      simp [returned,pairValue,VarList.pairValue,VarList.returnShape,shapeOfHOLExact,shapeEqHOL_eq_true]
    have resumed := CallNormal.return_execute source bodyPost name VarList.returnShape (ofString "decode_bytes_list") expressions
      (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum) body continuation callee VarList.returnShape returned args called funded actualBody shapePass
    have remaining := resumed.symm.trans run
    let next := CallNormal.continuationEntry source bodyPost name returned
    let innerPost := (evaluateHOLFiniteState next continuation).2
    have observed := congrArg Prod.fst remaining
    have endpoint : post=restore source name innerPost := (congrArg Prod.snd remaining).symm
    have nextControl : WitnessRadix.BackingLayout.control next=WitnessRadix.BackingLayout.control
        (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) := by
      by_cases empty : length=0
      · simp only [if_pos empty] at control ⊢; exact control
      · simp only [if_neg empty] at control ⊢; exact control
    have fields := evaluation_fields entry bodyPost body bodyResult bodyRun
    exact Or.inr ⟨next,innerPost,rfl,VarList.Records.of_memory bodyPost next input pointer array start length rfl records,countLimit,
      Blob.HeapInput.of_fields bodyPost next input pointer rfl rfl rfl bytes,sizes,cost,by change bodyPost.clock≤source.clock; omega,memory,
      fields.2.2.2,fields.1,fields.2.2.1,Prod.ext observed rfl,endpoint,nextControl⟩

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.caller_trace
