import InitECandidate.Solver.Input.BytesList.Tail
import InitECandidate.Solver.Input.VarList.RecordCells
import InitECandidate.Solver.Input.AllocationControl

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Normal execution of the whole actual byte-list decoder establishes all
concrete record lengths within maxb, including pointer0/count0 empty lists. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (enough : 2*(length/4)+4≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length) ∧
      VarList.Records post input pointer array start length ∧ VarList.decodedCount input start length≤limit.toNat ∧ Blob.HeapInput post input pointer ∧
      (∀ position<VarList.decodedCount input start length,
        (VarList.recordLength input start length (VarList.decodedCount input start length) position).toNat≤maximum.toNat) ∧
      source.clock-(2*(length/4)+2)≤post.clock ∧ post.clock≤source.clock ∧
      (∀ query : BitVec 64,query.toNat<array.toNat→post.memory query=source.memory query) := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (VarList.values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,arguments,VarList.values,localVar,p,n,l]
  rw [body_shape] at run
  obtain ⟨next,innerPost,returned,valueEq,localsEq,nextClock,controls,nextHeap,oldMemory,clockLower,clockUpper,nextRun,postEq,records,countLimit⟩:=
    VarList.caller_normal source post input pointer array limit start length heap inside domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode
      failCode exceptionShape "r" arguments tail args varCode (by omega) value run
  have tupleEq : returned=pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length) := by
    rw [valueEq]
    by_cases empty : length=0 <;>simp [pairValue,VarList.decodedArray,VarList.decodedCount,VarList.emptyValue,VarList.pairValue,empty]
  have rLocal : next.locals.lookup (ofString "r")=some (pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length)) := by
    rw [localsEq,tupleEq]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have mLocal : next.locals.lookup (ofString "maxb")=some (.val (.word maximum)) := by
    rw [localsEq]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "r"==ofString "maxb")=false from by decide] using m
  obtain ⟨nextDomain,nextCode,nextShapes⟩:=allocation_control_fields source next array
    (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4))) (length=0) controls
  obtain ⟨countBound,countSmall,cells⟩:=VarList.Records.cells next input pointer array start length (nextDomain.trans domain) records
  obtain ⟨result,target,paid,computed,bound,clock,frames,memory,outcome⟩:=tail_execute next (VarList.decodedArray array length) maximum
    (VarList.decodedCount input start length) (VarList.recordLength input start length (VarList.decodedCount input start length)) (by omega)
    rLocal mLocal (fun position small=>(cells position small).1) (fun position small=>(cells position small).2)
    (by rw [nextCode]; exact failCode) (by rw [nextShapes]; exact exceptionShape) (by omega)
  have equality:=nextRun.symm.trans computed
  have resultEq : some (.returned value)=result:=congrArg Prod.fst equality
  have targetEq : innerPost=target:=congrArg Prod.snd equality
  rcases outcome with normal|fault
  · have returnedEq : value=pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length) := by
      rw [normal.1] at resultEq
      cases resultEq
      rfl
    have postMemory : post.memory=next.memory := by
      rw [postEq,targetEq]
      exact memory
    have postDomain : post.memaddrs=next.memaddrs := by
      have eq:=congrArg PanSemStateFiniteExact.memaddrs frames
      change target.memaddrs=next.memaddrs at eq
      rw [postEq,targetEq]
      exact eq
    have postEndian : post.be=next.be := by
      have eq:=congrArg PanSemStateFiniteExact.be frames
      change target.be=next.be at eq
      rw [postEq,targetEq]
      exact eq
    have postClock : post.clock=next.clock-paid := by rw [postEq,targetEq]; exact clock
    refine ⟨returnedEq,VarList.Records.of_memory next post input pointer array start length postMemory records,countLimit,
      Blob.HeapInput.of_fields next post input pointer postMemory.symm postDomain.symm postEndian.symm nextHeap,normal.2.2,?_,?_,?_⟩
    · omega
    · omega
    · intro query before
      rw [postMemory]
      exact oldMemory query before
  · rw [fault] at resultEq
    cases resultEq

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.body_normal
