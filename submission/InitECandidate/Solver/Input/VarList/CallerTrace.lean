import InitECandidate.Solver.Input.VarList.BodyTrace
import InitECandidate.Solver.Input.VarList.NormalAnyClock
import InitECandidate.Solver.Input.VarList.Environment
import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.Input.NonTimeoutScopedCall

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual original variable-list call either propagates its real parser
error or resumes its arbitrary continuation with physical records and exact
allocation metadata. No future callee success or clock funding is assumed. -/
theorem caller_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit : BitVec 64) (start length : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+length≤input.length%2^64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*length≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit))
    (code : source.code.lookup (ofString "ssz_split_var_list")=some (formals,body,returnShape))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "ssz_split_var_list") expressions continuation) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64) ∧
      result=some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock-post.clock≤length/4+3) ∨
    (∃ next innerPost,next.locals=source.locals.update (ofString name,pairValue (decodedArray array length) (decodedCount input start length)) ∧
      WitnessRadix.BackingLayout.control next=WitnessRadix.BackingLayout.control
        (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) ∧
      Blob.HeapInput next input pointer ∧ (∀ query : BitVec 64,query.toNat<array.toNat → next.memory query=source.memory query) ∧
      Records next input pointer array start length ∧ decodedCount input start length≤limit.toNat ∧ next.clock≤source.clock ∧ source.clock-next.clock≤length/4+2 ∧
      evaluateHOLFiniteState next continuation=(result,innerPost) ∧ post=restore source name innerPost) := by
  classical
  obtain ⟨callee,called,p,n,l⟩ := environment source.code.lookup (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit code
  obtain ⟨funded,bodyNonTimeout⟩ := scoped_call_non_timeout source post (ofString name) returnShape (ofString "ssz_split_var_list") expressions
    (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit) body continuation callee returnShape args called result run notTimeout
  let entry := callEntryStateHOLFinite source callee
  let bodyResult := (evaluateHOLFiniteState entry body).1
  let bodyPost := (evaluateHOLFiniteState entry body).2
  have bodyRun : evaluateHOLFiniteState entry body=(bodyResult,bodyPost) := rfl
  have entryHeap : Blob.HeapInput entry input pointer := Blob.HeapInput.of_fields source entry input pointer rfl rfl rfl heap
  obtain ⟨cost,outcome⟩ := body_trace entry bodyPost input pointer array limit start length entryHeap inside p n l domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape bodyResult bodyRun bodyNonTimeout
  have bodyForward : bodyPost.clock≤source.clock-1 := evaluateHOLFiniteState_clock_le entry body
  rcases outcome with normal | rejected
  · obtain ⟨returned,same⟩ := normal
    have actualBody : evaluateHOLFiniteState entry body=(some (.returned returned),bodyPost) := Prod.ext same rfl
    obtain ⟨tuple,control,bytes,memory,records,countLimit,bodyCost,forward⟩ := normal_summary_any_clock entry bodyPost input pointer array limit start length entryHeap inside p n l domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape returned actualBody
    have shapePass : (shapeEqHOL (shapeOfHOLExact returned) returnShape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true := by
      rw [tuple]
      simp [pairValue,returnShape,shapeOfHOLExact,shapeEqHOL_eq_true]
    have resumed := CallNormal.return_execute source bodyPost name returnShape (ofString "ssz_split_var_list") expressions
      (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit) body continuation callee returnShape returned args called funded actualBody shapePass
    have remaining := resumed.symm.trans run
    let next := CallNormal.continuationEntry source bodyPost name returned
    let innerPost := (evaluateHOLFiniteState next continuation).2
    have observed := congrArg Prod.fst remaining
    have endpoint : post=restore source name innerPost := (congrArg Prod.snd remaining).symm
    have nextControl : WitnessRadix.BackingLayout.control next = WitnessRadix.BackingLayout.control
        (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) := by
      by_cases empty : length=0
      · simp only [if_pos empty] at control ⊢; exact control
      · simp only [if_neg empty] at control ⊢; exact control
    have nextHeap := Blob.HeapInput.of_fields bodyPost next input pointer rfl rfl rfl bytes
    have locals : next.locals=source.locals.update (ofString name,pairValue (decodedArray array length) (decodedCount input start length)) := by change source.locals.update (ofString name,returned)=_; rw [tuple]
    change source.clock-1-bodyPost.clock≤length/4+1 at bodyCost
    exact Or.inr ⟨next,innerPost,locals,nextControl,nextHeap,memory,Records.of_memory bodyPost next input pointer array start length rfl records,countLimit,
      by change bodyPost.clock≤source.clock; omega,by change source.clock-bodyPost.clock≤length/4+2; omega,Prod.ext observed rfl,endpoint⟩
  · obtain ⟨error,allowed,same⟩ := rejected
    have actualBody : evaluateHOLFiniteState entry body=(some (.exception (ofString "SszErr") (.val (.word error))),bodyPost) := Prod.ext same rfl
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
    simp only [args,called,if_neg (show source.clock≠0 by omega)] at run
    rw [actualBody] at run
    have endpoint : post.clock=bodyPost.clock := by have h := congrArg (fun output => output.2.clock) run; exact h.symm
    change source.clock-1-bodyPost.clock≤length/4+2 at cost
    exact Or.inl ⟨error,allowed,(congrArg Prod.fst run).symm,by rw [endpoint]; omega⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.caller_trace
