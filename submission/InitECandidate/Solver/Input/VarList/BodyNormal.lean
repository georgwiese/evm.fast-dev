import InitECandidate.Solver.Input.VarList.Allocation
import InitECandidate.Solver.Input.VarList.EncodedCount

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- From a genuine nonempty normal return of the whole fixed variable-list
decoder: derive the count/header facts, real allocation/record contents, exact
clock/global update, copied input and all old memory outside the fresh array.
Natural allocator room and initial runtime facts remain explicit. -/
theorem nonempty_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit : BitVec 64) (start length : Nat) (nonempty : 0<length)
    (heap : Blob.HeapInput source input pointer) (inside : start+length≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (arrayRoom : array.toNat+16*(Guest.GasLimit.le32 input start/4)≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : length/4+2≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ plan : Plan input,
      plan.inputPointer=pointer ∧ plan.array=array ∧ plan.start=start ∧ plan.length=length ∧ plan.count=Guest.GasLimit.le32 input start/4 ∧
      value=pairValue array (Guest.GasLimit.le32 input start/4) ∧
      post.clock=source.clock-(Guest.GasLimit.le32 input start/4+1) ∧
      WitnessRadix.BackingLayout.control post=WitnessRadix.BackingLayout.control
        (WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) ∧
      Blob.HeapInput post input pointer ∧ ArrayFrame source post input plan ∧ Complete post input plan (BitVec.ofNat 64 length) ∧
      ∀ position,position<plan.count→Offsets.ValidAt (BitVec.ofNat 64 (Guest.GasLimit.le32 input start)) (BitVec.ofNat 64 length) (currentWord input start) position := by
  classical
  have normal:=normal_entry source post input pointer limit start length heap inside p n l failCode exceptionShape (by omega) value run
  rcases normal with empty|parsed
  · omega
  · obtain ⟨minimum,positive,header,firstUpper,limitUpper,innerPost,allocationRun,postRestore⟩:=parsed
    let plan : Plan input := {
      inputPointer:=pointer, array:=array, start:=start, length:=length, count:=Guest.GasLimit.le32 input start/4,
      positive:=positive, header:=by omega, slice:=inside, inputLower:=lower, inputAligned:=aligned,
      arrayAligned:=arrayAligned, arrayAfter:=arrayAfter, arrayRoom:=arrayRoom }
    let first:=BitVec.ofNat 64 (Guest.GasLimit.le32 input start)
    let entered:=bind source "first" first
    let ready:=counted entered first
    have firstHeap : Blob.HeapInput entered input pointer := Blob.HeapInput.bind source input pointer "first" first heap
    have readyHeap : Blob.HeapInput ready input plan.inputPointer := Blob.HeapInput.bind entered input pointer "count" (countWord first) firstHeap
    have rp : ready.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))) :=
      (bind_lookup_other entered "count" "p" _ (by decide)).trans ((bind_lookup_other source "first" "p" first (by decide)).trans p)
    have rf : ready.locals.lookup (ofString "first")=some (.val (.word first)) :=
      (bind_lookup_other entered "count" "first" _ (by decide)).trans (bind_lookup_same _ _ _)
    have rn : ready.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) :=
      (bind_lookup_other entered "count" "len" _ (by decide)).trans ((bind_lookup_other source "first" "len" first (by decide)).trans n)
    have rc : ready.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))) := by
      have encoded : countWord first=BitVec.ofNat 64 plan.count := count_encode input start
      exact (bind_lookup_same entered "count" (countWord first)).trans
        (congrArg (fun word : BitVec 64=>some (ValueHOL.val (HolWordLab.word word))) encoded)
    have countBound : plan.count≤length/4 := by change Guest.GasLimit.le32 input start/4≤length/4; omega
    obtain ⟨result,target,paid,computed,bound,clock,control,heapAfter,arrayFrame,outcome⟩:=allocation_execute ready input plan first (BitVec.ofNat 64 length) readyHeap domain
      rp rf rn rc failCode exceptionShape heapGlobal allocCode (by change plan.count+2≤source.clock; omega)
    have equal:=allocationRun.symm.trans computed
    have resultEq : some (.returned value)=result := congrArg Prod.fst equal
    have targetEq : innerPost=target := congrArg Prod.snd equal
    rcases outcome with normal|fault
    · have outputs:=resultEq.trans normal.1
      have valueEq : value=pairValue plan.array plan.count := by cases outputs; rfl
      have finalPost : post=restore source "first" (restore entered "count" target) := by rw [postRestore,targetEq]
      have postHeap : Blob.HeapInput post input pointer := by
        rw [finalPost]
        exact Blob.HeapInput.restore source _ input pointer "first" (Blob.HeapInput.restore entered target input pointer "count" heapAfter)
      have postFrame : ArrayFrame source post input plan := by
        rw [finalPost]
        intro query outside
        exact arrayFrame query outside
      have postControl : WitnessRadix.BackingLayout.control post=WitnessRadix.BackingLayout.control (WitnessRadix.PersistentAlloc.post source array (BitVec.ofNat 64 (16*plan.count))) := by
        rw [finalPost]
        exact control
      have postClock : post.clock=source.clock-(plan.count+1) := by
        rw [finalPost]
        change target.clock=source.clock-(plan.count+1)
        change target.clock=source.clock-paid at clock
        rw [clock,normal.2.1]
      have complete : Complete post input plan (BitVec.ofNat 64 length) := by
        rw [finalPost]
        exact normal.2.2.1
      exact ⟨plan,rfl,rfl,rfl,rfl,rfl,valueEq,postClock,postControl,postHeap,postFrame,complete,normal.2.2.2⟩
    · rw [fault] at resultEq
      cases resultEq

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.nonempty_normal
