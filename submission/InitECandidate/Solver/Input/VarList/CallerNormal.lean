import InitECandidate.Solver.Input.VarList.NormalSummary
import InitECandidate.Solver.Input.VarList.Environment
import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.Input.VarList.CountLimit

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal real variable-list call resumes its actual caller continuation with
the correct tuple value and saved caller locals. Copied input and prior heap
words preserve; empty/nonempty calls include their exact call-clock payment. -/
theorem caller_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (enough : length/4+3≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "ssz_split_var_list") expressions continuation)=(some (.returned value),post)) :
    ∃ next innerPost returned,
      returned=(if length=0 then emptyValue else pairValue array (Guest.GasLimit.le32 input start/4)) ∧
      next.locals=source.locals.update (ofString name,returned) ∧
      next.clock=source.clock-1-(if length=0 then 0 else Guest.GasLimit.le32 input start/4+1) ∧
      WitnessRadix.BackingLayout.control next=WitnessRadix.BackingLayout.control
        (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) ∧
      Blob.HeapInput next input pointer ∧
      (∀ query : BitVec 64,query.toNat<array.toNat→next.memory query=source.memory query) ∧
      source.clock-(length/4+2)≤next.clock ∧ next.clock≤source.clock ∧
      evaluateHOLFiniteState next continuation=(some (.returned value),innerPost) ∧ post=restore source name innerPost ∧ Records next input pointer array start length ∧ decodedCount input start length≤limit.toNat := by
  classical
  obtain ⟨callee,called,p,n,l⟩:=environment source.code.lookup (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit code
  obtain ⟨bodyPost,returned,bodyRun⟩:=CallNormal.callee_return source post (ofString name) returnShape (ofString "ssz_split_var_list") expressions
    (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit) body continuation callee returnShape args called (by omega) value run
  let entry:=callEntryStateHOLFinite source callee
  have entryHeap : Blob.HeapInput entry input pointer := Blob.HeapInput.of_fields source entry input pointer rfl rfl rfl heap
  obtain ⟨valueEq,bodyClock,bodyControl,bodyHeap,oldMemory,bodyLower,bodyUpper⟩:=normal_summary entry bodyPost input pointer array limit start length
    entryHeap inside p n l domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape (by change length/4+2≤source.clock-1; omega) returned bodyRun
  have records:=normal_records entry bodyPost input pointer array limit start length entryHeap inside p n l domain lower aligned arrayAligned arrayAfter room
    heapGlobal allocCode failCode exceptionShape (by change length/4+2≤source.clock-1; omega) returned bodyRun
  have countLimit:=normal_count_limit entry bodyPost input pointer limit start length entryHeap inside p n l failCode exceptionShape (by change 1≤source.clock-1; omega) returned bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact returned) returnShape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true := by
    rw [valueEq]
    by_cases empty : length=0
    · simp only [if_pos empty]
      simp [emptyValue,pairValue,returnShape,shapeOfHOLExact,shapeEqHOL_eq_true]
    · simp only [if_neg empty]
      simp [emptyValue,pairValue,returnShape,shapeOfHOLExact,shapeEqHOL_eq_true]
  have actual:=CallNormal.return_execute source bodyPost name returnShape (ofString "ssz_split_var_list") expressions
    (values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit) body continuation callee returnShape returned args called (by omega) bodyRun shapePass
  have normal:=actual.symm.trans run
  let next:=CallNormal.continuationEntry source bodyPost name returned
  have result : (evaluateHOLFiniteState next continuation).1=some (.returned value) := congrArg Prod.fst normal
  have postEq : post=restore source name (evaluateHOLFiniteState next continuation).2 := (congrArg Prod.snd normal).symm
  have nextHeap : Blob.HeapInput next input pointer := Blob.HeapInput.of_fields bodyPost next input pointer rfl rfl rfl bodyHeap
  have nextControl : WitnessRadix.BackingLayout.control next=WitnessRadix.BackingLayout.control
      (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) := by
    by_cases empty : length=0
    · simp only [if_pos empty] at bodyControl ⊢
      exact bodyControl
    · simp only [if_neg empty] at bodyControl ⊢
      exact bodyControl
  refine ⟨next,(evaluateHOLFiniteState next continuation).2,returned,valueEq,rfl,bodyClock,nextControl,nextHeap,?_,?_,?_,Prod.ext result rfl,postEq,Records.of_memory bodyPost next input pointer array start length rfl records,countLimit⟩
  · intro query before
    exact oldMemory query before
  · change source.clock-(length/4+2)≤bodyPost.clock
    change source.clock-1-(length/4+1)≤bodyPost.clock at bodyLower
    omega
  · change bodyPost.clock≤source.clock
    change bodyPost.clock≤source.clock-1 at bodyUpper
    omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.caller_normal
