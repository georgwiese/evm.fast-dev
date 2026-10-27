import InitECandidate.Solver.Input.VarList.MemoryFrame

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The entire real record loop on arbitrary copied offsets. It either returns
normally with the exact store/update walk and every range/order fact, or raises
SszErr23. Every path preserves copied input and control, within rounds+1 clocks. -/
theorem any_loop (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index rounds : Nat) (finish : index+rounds=plan.count) (previous first total : BitVec 64)
    (heap : Blob.HeapInput source input plan.inputPointer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word plan.array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (p : source.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))))
    (previousLocal : source.locals.lookup (ofString "prev")=some (.val (.word previous)))
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (c : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))))
    (previousIndex : 0<index→previous=currentWord input plan.start (index-1))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : rounds+1≤source.clock) :
    ∃ result target paid,
      evaluateHOLFiniteState source loop=(result,target) ∧ paid≤rounds+1 ∧ target.clock=source.clock-paid ∧
      WitnessRadix.BackingLayout.control target=WitnessRadix.BackingLayout.control source ∧
      Blob.HeapInput target input plan.inputPointer ∧ ArrayFrame source target input plan ∧
      ((result=none ∧ paid=rounds ∧ target=walk source input plan index previous rounds ∧
        ∀ position,index≤position→position<plan.count→Offsets.ValidAt first total (currentWord input plan.start) position) ∨
        result=some (.exception (ofString "SszErr") (.val (.word 23#64)))) := by
  classical
  have countSmall : plan.count<2^63 := by have h:=plan.count_small; omega
  induction rounds generalizing source index previous with
  | zero=>
    have inactive : ¬index<plan.count := by omega
    have test:=loop_test_read source index plan.count (by omega) countSmall i c
    simp only [if_neg inactive] at test
    have finiteTest : evalHOLFinite source loopTest=some (.val (.word 0#64)) := test
    refine ⟨none,source,0,?_,by omega,by simp,rfl,heap,ArrayFrame.refl source input plan,Or.inl ⟨rfl,rfl,rfl,?_⟩⟩
    · rw [loop_shape,evaluateHOLFiniteState_while_total,finiteTest]
      simp
    · intro position low high
      omega
  | succ rounds ih=>
    have active : index<plan.count := by omega
    have nonzero : source.clock≠0 := by omega
    let entry:=decClockHOLFinite source
    have entryHeap : Blob.HeapInput entry input plan.inputPointer := Blob.HeapInput.of_fields source entry input plan.inputPointer rfl rfl rfl heap
    let current:=currentWord input plan.start index
    by_cases bad : badRecord current first total previous
    · obtain ⟨bodyRun,bodyFrame,bodyHeap⟩:=fault_body entry input plan index active previous first total entryHeap i p previousLocal f n bad failCode exceptionShape
        (by change 1≤source.clock-1; omega)
      let target:=failedIteration entry input plan index
      have clock : target.clock=source.clock-2 := by
        have h:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.clock) bodyFrame
        change target.clock=source.clock-1-1 at h
        omega
      have control:=WitnessRadix.BackingLayout.control_of_frame target {entry with clock:=entry.clock-1} bodyFrame
      have targetControl : WitnessRadix.BackingLayout.control target=WitnessRadix.BackingLayout.control source := by
        exact control.trans (show WitnessRadix.BackingLayout.control {entry with clock:=entry.clock-1}=WitnessRadix.BackingLayout.control source from rfl)
      have run:=active_unroll source target index plan.count countSmall active i c nonzero
        (some (.exception (ofString "SszErr") (.val (.word 23#64)))) bodyRun (by rw [clock]; omega)
      have arrayFrame : ArrayFrame source target input plan := by
        intro query outside
        exact failed_iteration_frame entry input plan index query outside
      refine ⟨_,target,2,?_,by omega,clock,targetControl,bodyHeap,arrayFrame,Or.inr rfl⟩
      exact run
    · obtain ⟨bodyRun,bodyHeap⟩:=valid_body entry input plan index active previous first total entryHeap domain a i p previousLocal f n bad
      let next:=iteration entry input plan index previous
      have nextClock : next.clock=source.clock-1 := iteration_clock entry input plan index previous
      have nextControl : WitnessRadix.BackingLayout.control next=WitnessRadix.BackingLayout.control source := by
        exact (iteration_control entry input plan index previous).trans (show WitnessRadix.BackingLayout.control entry=WitnessRadix.BackingLayout.control source from rfl)
      have na : next.locals.lookup (ofString "arr")=some (.val (.word plan.array)) :=
        (iteration_other entry input plan index previous "arr" (by decide) (by decide) (by decide)).trans a
      have np : next.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))) :=
        (iteration_other entry input plan index previous "p" (by decide) (by decide) (by decide)).trans p
      have nf : next.locals.lookup (ofString "first")=some (.val (.word first)) :=
        (iteration_other entry input plan index previous "first" (by decide) (by decide) (by decide)).trans f
      have nn : next.locals.lookup (ofString "len")=some (.val (.word total)) :=
        (iteration_other entry input plan index previous "len" (by decide) (by decide) (by decide)).trans n
      have nc : next.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))) :=
        (iteration_other entry input plan index previous "count" (by decide) (by decide) (by decide)).trans c
      have nextPrevious : 0<index+1→currentWord input plan.start index=currentWord input plan.start (index+1-1) := by
        intro positive
        simp
      obtain ⟨result,target,paid,tailRun,bound,clock,control,heapAfter,arrayFrame,outcome⟩:=ih next (index+1) (by omega) current bodyHeap domain
        na (iteration_index entry input plan index previous) np (iteration_previous entry input plan index previous) nf nn nc nextPrevious
        failCode exceptionShape (by rw [nextClock]; omega)
      have continued : evaluateHOLFiniteState source loop=evaluateHOLFiniteState next loop :=
        active_unroll source next index plan.count countSmall active i c nonzero none bodyRun (by rw [nextClock]; exact Nat.le_refl _)
      rw [tailRun] at continued
      have finalClock : target.clock=source.clock-(paid+1) := by rw [clock,nextClock]; omega
      have headFrame : ArrayFrame source next input plan := by
        intro query outside
        exact iteration_frame entry input plan index active previous query outside
      refine ⟨result,target,paid+1,continued,by omega,finalClock,control.trans nextControl,heapAfter,headFrame.trans arrayFrame,?_⟩
      rcases outcome with normal|fault
      · refine Or.inl ⟨normal.1,by omega,normal.2.2.1,?_⟩
        intro position low high
        by_cases same : position=index
        · subst position
          have bounds : first.toNat≤current.toNat ∧ current.toNat≤total.toNat ∧ previous.toNat≤current.toNat := by
            unfold badRecord at bad
            omega
          refine ⟨bounds.1,bounds.2.1,?_⟩
          intro positive
          rw [←previousIndex positive]
          exact bounds.2.2
        · exact normal.2.2.2 position (by omega) high
      · exact Or.inr fault

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.any_loop
