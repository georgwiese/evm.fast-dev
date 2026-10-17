import InitECandidate.Solver.Input.VarList.Complete

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All actual record-loop outcomes and the genuine final store/pair return.
Normal execution initializes the complete record array in exactly count clocks;
any malformed offset raises SszErr23 within count+1 clocks. -/
theorem loop_return (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (first total : BitVec 64) (heap : Blob.HeapInput source input plan.inputPointer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word plan.array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (p : source.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))))
    (previousLocal : source.locals.lookup (ofString "prev")=some (.val (.word first)))
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (c : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : plan.count+1≤source.clock) :
    ∃ result target paid,
      evaluateHOLFiniteState source (.seq loop afterLoop)=(result,target) ∧ paid≤plan.count+1 ∧ target.clock=source.clock-paid ∧
      WitnessRadix.BackingLayout.control target=WitnessRadix.BackingLayout.control source ∧ Blob.HeapInput target input plan.inputPointer ∧
      ((result=some (.returned (pairValue plan.array plan.count)) ∧ paid=plan.count ∧ Complete target input plan total ∧
          ∀ position,position<plan.count→Offsets.ValidAt first total (currentWord input plan.start) position) ∨
        result=some (.exception (ofString "SszErr") (.val (.word 23#64)))) := by
  classical
  obtain ⟨result,middle,paid,loopRun,bound,clock,control,middleHeap,outcome⟩:=any_loop source input plan 0 plan.count (by simp) first first total
    heap domain a i p previousLocal f n c (by intro positive; omega) failCode exceptionShape enough
  rcases outcome with normal|fault
  · have loopNone : evaluateHOLFiniteState source loop=(none,middle) := by simpa only [normal.1] using loopRun
    have middleWalk : middle=walk source input plan 0 first plan.count := normal.2.2.1
    have middleA : middle.locals.lookup (ofString "arr")=some (.val (.word plan.array)) := by
      rw [middleWalk,walk_other _ _ _ _ _ _ "arr" (by decide) (by decide) (by decide)]
      exact a
    have middleC : middle.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))) := by
      rw [middleWalk,walk_other _ _ _ _ _ _ "count" (by decide) (by decide) (by decide)]
      exact c
    have middleN : middle.locals.lookup (ofString "len")=some (.val (.word total)) := by
      rw [middleWalk,walk_other _ _ _ _ _ _ "len" (by decide) (by decide) (by decide)]
      exact n
    have middlePrev : middle.locals.lookup (ofString "prev")=some (.val (.word (currentWord input plan.start (plan.count-1)))) := by
      rw [middleWalk]
      simpa only [Nat.zero_add] using walk_previous source input plan 0 plan.count first plan.positive
    have middleDomain : middle.memaddrs=InitE.ordinaryDomain := by
      have h:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memaddrs) control
      have eq : middle.memaddrs=source.memaddrs := h
      exact eq.trans domain
    have filled : Filled middle input plan plan.count := by
      rw [middleWalk]
      simpa only [Nat.zero_add] using walk_filled source input plan 0 plan.count (by simp) first (filled_zero source input plan) (by intro positive; omega)
    obtain ⟨returned,finalHeap,finalControl⟩:=return_execute middle input plan total (currentWord input plan.start (plan.count-1))
      middleHeap middleDomain middleA middleC middleN middlePrev
    let target:=emptyLocalsHOLFinite (finished middle plan.array plan.count total (currentWord input plan.start (plan.count-1)))
    have complete : Complete target input plan total := complete_finished middle input plan total _ filled rfl
    have continued:=WitnessRadix.StateSteps.next_sequence source middle loop afterLoop loopNone (by rw [clock]; omega)
    rw [returned] at continued
    have finalClock : target.clock=source.clock-plan.count := by
      change middle.clock=source.clock-plan.count
      rw [clock,normal.2.1]
    refine ⟨_,target,plan.count,continued,by omega,finalClock,finalControl.trans control,finalHeap,Or.inl ⟨rfl,rfl,complete,?_⟩⟩
    intro position small
    exact normal.2.2.2 position (by omega) small
  · have loopFault : evaluateHOLFiniteState source loop=(some (.exception (ofString "SszErr") (.val (.word 23#64))),middle) := by
      simpa only [fault] using loopRun
    have stopped:=WitnessRadix.StateSteps.stopped_sequence source middle loop afterLoop
      (.exception (ofString "SszErr") (.val (.word 23#64))) loopFault (by rw [clock]; omega)
    exact ⟨_,middle,paid,stopped,bound,clock,control,middleHeap,Or.inr rfl⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.loop_return
