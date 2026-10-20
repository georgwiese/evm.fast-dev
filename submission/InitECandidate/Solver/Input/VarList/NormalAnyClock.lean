import InitECandidate.Solver.Input.VarList.Records
import InitECandidate.Solver.Input.VarList.CountLimit
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual variable-list normal data at any clock budget: exact returned pair,
physical records, count limit, original allocation/control and earlier words. -/
theorem normal_summary_any_clock (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit : BitVec 64) (start length : Nat)
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
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned value),post)) :
    value = pairValue (decodedArray array length) (decodedCount input start length) ∧
      WitnessRadix.BackingLayout.control post = WitnessRadix.BackingLayout.control
        (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) ∧
      Blob.HeapInput post input pointer ∧ (∀ query : BitVec 64,query.toNat<array.toNat → post.memory query=source.memory query) ∧
      Records post input pointer array start length ∧ decodedCount input start length≤limit.toNat ∧ source.clock-post.clock≤length/4+1 ∧ post.clock≤source.clock := by
  classical
  let padding := length/4+2
  have paddedRun := panPropsEvaluateAddClockEq body source (some (.returned value)) post padding ⟨run,by intro impossible; cases impossible⟩
  obtain ⟨returned,clock,control,bytes,memory,lowerClock,upperClock⟩ := normal_summary {source with clock:=source.clock+padding} {post with clock:=post.clock+padding}
    input pointer array limit start length heap inside p n l domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape
    (by change length/4+2≤source.clock+padding; dsimp only [padding]; omega) value paddedRun
  have records := normal_records {source with clock:=source.clock+padding} {post with clock:=post.clock+padding}
    input pointer array limit start length heap inside p n l domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape
    (by change length/4+2≤source.clock+padding; dsimp only [padding]; omega) value paddedRun
  have countLimit := normal_count_limit {source with clock:=source.clock+padding} {post with clock:=post.clock+padding}
    input pointer limit start length heap inside p n l failCode exceptionShape (by change 1≤source.clock+padding; dsimp only [padding]; omega) value paddedRun
  have tuple : value = pairValue (decodedArray array length) (decodedCount input start length) := by
    rw [returned]
    by_cases empty : length=0 <;> simp [decodedArray,decodedCount,empty,emptyValue,pairValue]
  have actualControl : WitnessRadix.BackingLayout.control post = WitnessRadix.BackingLayout.control
      (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) := by
    by_cases empty : length=0
    · simp only [if_pos empty] at control ⊢; exact control
    · simp only [if_neg empty] at control ⊢; exact control
  change source.clock+padding-(length/4+1)≤post.clock+padding at lowerClock
  change post.clock+padding≤source.clock+padding at upperClock
  exact ⟨tuple,actualControl,Blob.HeapInput.of_fields _ post input pointer rfl rfl rfl bytes,memory,
    Records.of_memory _ post input pointer array start length rfl records,countLimit,by omega,by omega⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.normal_summary_any_clock
