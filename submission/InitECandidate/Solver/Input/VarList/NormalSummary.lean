import InitECandidate.Solver.Input.VarList.BodyNormal

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole fixed decoder normal-return summary, including its genuine empty
case. A conservative natural allocation budget suffices; no first-offset or
record-count validity is assumed. Earlier heap words and copied bytes preserve. -/
theorem normal_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : length/4+2≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=(if length=0 then emptyValue else pairValue array (Guest.GasLimit.le32 input start/4)) ∧
    post.clock=source.clock-(if length=0 then 0 else Guest.GasLimit.le32 input start/4+1) ∧
    WitnessRadix.BackingLayout.control post=WitnessRadix.BackingLayout.control
      (if length=0 then source else WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) ∧
    Blob.HeapInput post input pointer ∧
    (∀ query : BitVec 64,query.toNat<array.toNat→post.memory query=source.memory query) ∧
    source.clock-(length/4+1)≤post.clock ∧ post.clock≤source.clock := by
  classical
  by_cases empty : length=0
  · have actual:=entry_execute source input pointer start length heap inside p n failCode exceptionShape (by omega)
    simp only [if_pos empty] at actual
    have eq:=actual.symm.trans run
    have values:=congrArg Prod.fst eq
    have valueEq : value=emptyValue := by cases values; rfl
    have postEq : post=emptyLocalsHOLFinite source := (congrArg Prod.snd eq).symm
    simp only [if_pos empty]
    refine ⟨valueEq,?_,?_,?_,?_,?_,?_⟩
    · rw [postEq]
      change source.clock=source.clock-0
      omega
    · rw [postEq]
      rfl
    · rw [postEq]
      exact Blob.HeapInput.of_fields source (emptyLocalsHOLFinite source) input pointer rfl rfl rfl heap
    · intro query before
      rw [postEq]
      rfl
    · rw [postEq]
      change source.clock-(length/4+1)≤source.clock
      omega
    · rw [postEq]
      exact Nat.le_refl _
  · have positive : 0<length := by omega
    have parsed:=normal_entry source post input pointer limit start length heap inside p n l failCode exceptionShape (by omega) value run
    have countBound : Guest.GasLimit.le32 input start/4≤length/4 := by
      rcases parsed with nil|list
      · omega
      · obtain ⟨minimum,countPositive,header,firstUpper,limitUpper,rest⟩:=list
        omega
    have allocationRoom : array.toNat+16*(Guest.GasLimit.le32 input start/4)≤33806089496 := by omega
    obtain ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,valueEq,clockEq,control,postHeap,frame,complete,valid⟩:=nonempty_normal source post input pointer array limit start length positive heap inside p n l
      domain lower aligned arrayAligned arrayAfter allocationRoom heapGlobal allocCode failCode exceptionShape enough value run
    simp only [if_neg empty]
    refine ⟨valueEq,clockEq,control,postHeap,?_,?_,?_⟩
    · intro query before
      apply frame query
      left
      rw [arrayEq]
      exact before
    · rw [clockEq]
      omega
    · rw [clockEq]
      omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.normal_summary
