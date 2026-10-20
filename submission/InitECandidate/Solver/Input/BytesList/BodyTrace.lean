import InitECandidate.Solver.Input.BytesList.TailTrace
import InitECandidate.Solver.Input.VarList.CallerTrace
import InitECandidate.Solver.Input.VarList.RecordCells
import InitECandidate.Solver.Input.AllocationControl

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete actual original byte-list decoder, including every malformed
variable-list exit and SszErr70 size rejection. Its actual normal result
retains physical records, count/size checks, allocation and prior heap words. -/
theorem body_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit maximum : BitVec 64) (start length : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+length≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*length≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (m : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤2*(length/4)+3 ∧
    ((∃ error : BitVec 64,(error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨
      (result=some (.returned (pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length))) ∧
       VarList.Records post input pointer array start length ∧ VarList.decodedCount input start length≤limit.toNat ∧ Blob.HeapInput post input pointer ∧
       (∀ position<VarList.decodedCount input start length,(VarList.recordLength input start length (VarList.decodedCount input start length) position).toNat≤maximum.toNat) ∧
       (∀ query : BitVec 64,query.toNat<array.toNat → post.memory query=source.memory query) ∧
       WitnessRadix.BackingLayout.control post=WitnessRadix.BackingLayout.control
         (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))))) := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments = some (VarList.values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,arguments,VarList.values,localVar,p,n,l]
  rw [body_shape] at run
  rcases VarList.caller_trace source post input pointer array limit start length heap inside domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode
    failCode exceptionShape "r" arguments tail args varCode result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    exact ⟨by omega,Or.inl ⟨error,by rcases allowed with rfl | rfl | rfl | rfl <;> simp,same⟩⟩
  obtain ⟨next,innerPost,localsEq,controls,nextHeap,oldMemory,records,countLimit,clockUpper,clockCost,nextRun,postEq⟩ := normal
  have rLocal : next.locals.lookup (ofString "r")=some (pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length)) := by
    rw [localsEq]; simp [HolFiniteMapExact.lookup_update,FUPDATE,pairValue]
  have mLocal : next.locals.lookup (ofString "maxb")=some (.val (.word maximum)) := by
    rw [localsEq]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "r"==ofString "maxb")=false from by decide] using m
  obtain ⟨nextDomain,nextCode,nextShapes⟩ := allocation_control_fields source next array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4))) (length=0) controls
  obtain ⟨countBound,countSmall,cells⟩ := VarList.Records.cells next input pointer array start length (nextDomain.trans domain) records
  obtain ⟨tailCost,frames,memory,outcome⟩ := tail_trace next innerPost (VarList.decodedArray array length) maximum (VarList.decodedCount input start length)
    (VarList.recordLength input start length (VarList.decodedCount input start length)) (by omega) rLocal mLocal
    (fun position small=>(cells position small).1) (fun position small=>(cells position small).2)
    (by rw [nextCode]; exact failCode) (by rw [nextShapes]; exact exceptionShape) result nextRun notTimeout
  have tailForward := evaluateHOLFiniteState_clock_le next tail
  rw [nextRun] at tailForward
  change innerPost.clock≤next.clock at tailForward
  have postClock : post.clock=innerPost.clock := by rw [postEq]; rfl
  have cost : source.clock-post.clock≤2*(length/4)+3 := by rw [postClock]; omega
  refine ⟨cost,?_⟩
  rcases outcome with normal | fault
  · have postMemory : post.memory=next.memory := by rw [postEq]; exact memory
    have postDomain : post.memaddrs=next.memaddrs := by
      have h := congrArg PanSemStateFiniteExact.memaddrs frames
      rw [postEq]; exact h
    have postEndian : post.be=next.be := by
      have h := congrArg PanSemStateFiniteExact.be frames
      rw [postEq]; exact h
    have postControl : WitnessRadix.BackingLayout.control post=WitnessRadix.BackingLayout.control next := by
      rw [postEq]
      have h := congrArg WitnessRadix.BackingLayout.control frames
      exact h
    exact Or.inr ⟨normal.1,VarList.Records.of_memory next post input pointer array start length postMemory records,countLimit,
      Blob.HeapInput.of_fields next post input pointer postMemory.symm postDomain.symm postEndian.symm nextHeap,normal.2,
      by intro query before; rw [postMemory]; exact oldMemory query before,postControl.trans controls⟩
  · exact Or.inl ⟨70#64,Or.inr (Or.inr (Or.inr (Or.inr rfl))),fault⟩

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.body_trace
