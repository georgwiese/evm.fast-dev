import InitECandidate.Solver.Input.PayloadOffsetsStores

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem guard_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array total : BitVec 64)
    (a : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) guardArguments=
      some (Offsets.arguments array 540#64 total 4) := by
  classical
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,guardArguments,Offsets.arguments,Header.offsets,localVar,a,n]

/-- Normal execution through all four stores and the real payload validator
proves its fixed offset and all ranges/order. Every rejected array is covered. -/
theorem offsets_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array total : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (l0 : source.locals.lookup (ofString "o_extra")=some (.val (.word (offsetWords input 0))))
    (l1 : source.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))))
    (l2 : source.locals.lookup (ofString "o_wd")=some (.val (.word (offsetWords input 2))))
    (l3 : source.locals.lookup (ofString "o_bal")=some (.val (.word (offsetWords input 3))))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat)
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 6≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source offsetBody=(some (.returned value),post)) :
    offsetWords input 0=540#64 ∧ (∀ position<4,Offsets.ValidAt 540#64 total (offsetWords input) position) ∧
      ∃ next paid,paid≤6 ∧ next={offsetsStored source input array with clock:=source.clock-paid} ∧
        Blob.HeapInput next input pointer ∧ evaluateHOLFiniteState next offsetContinuation=(some (.returned value),post) := by
  classical
  obtain ⟨s0,s1,s2,s3,storedHeap,mapped,cells⟩:=offsets_stores source input pointer array heap arrayGlobal l0 l1 l2 l3 domain pointerAligned arrayAligned upper arrayLower arrayBefore
  let stored:=offsetsStored source input array
  have actual : evaluateHOLFiniteState source offsetBody=evaluateHOLFiniteState stored (.seq guardCall offsetContinuation) := by
    rw [offset_body_shape,
      WitnessRadix.StateSteps.next_sequence source (extraStored source input array) _ _ s0 (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence (extraStored source input array) (transactionsStored source input array) _ _ s1 (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence (transactionsStored source input array) (withdrawalsStored source input array) _ _ s2 (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence (withdrawalsStored source input array) stored _ _ s3 (Nat.le_refl _)]
  have args:=guard_arguments_read stored array total arrayGlobal n
  obtain ⟨result,target,paid,guardRun,bound,frame,outcome⟩:=Offsets.call_execute stored guardArguments array 540#64 total (offsetWords input) 4
    (by decide) (by decide) args code failCode exceptionShape mapped cells enough
  have clock : target.clock=source.clock-paid := by
    have h:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.clock) frame
    exact h
  have tailRun : evaluateHOLFiniteState stored (.seq guardCall offsetContinuation)=(some (.returned value),post) := actual.symm.trans run
  rcases outcome with normal|fault
  · have guardNone : evaluateHOLFiniteState stored guardCall=(none,target) := by simpa only [normal.1,guardCall] using guardRun
    have continued:=WitnessRadix.StateSteps.next_sequence stored target guardCall offsetContinuation guardNone (by change target.clock≤source.clock; rw [clock]; omega)
    rw [continued] at tailRun
    have targetEq:=Request.state_from_frame stored target paid frame normal.2.2.1
    have storedClock : stored.clock=source.clock := rfl
    rw [storedClock] at targetEq
    have memEq:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memory) frame
    have domainEq:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memaddrs) frame
    have endianEq:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.be) frame
    have heapAfter:=Blob.HeapInput.of_fields stored target input pointer memEq.symm domainEq.symm endianEq.symm storedHeap
    exact ⟨normal.2.1,normal.2.2.2,target,paid,bound,targetEq,heapAfter,tailRun⟩
  · obtain ⟨error,allowed,resultEq⟩:=fault
    have guardFault : evaluateHOLFiniteState stored guardCall=
        (some (.exception (ofString "SszErr") (.val (.word error))),target) := by simpa only [resultEq,guardCall] using guardRun
    have stopped:=WitnessRadix.StateSteps.stopped_sequence stored target guardCall offsetContinuation
      (.exception (ofString "SszErr") (.val (.word error))) guardFault (by change target.clock≤source.clock; rw [clock]; omega)
    rw [stopped] at tailRun
    have impossible:=congrArg Prod.fst tailRun
    cases impossible

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.guard_arguments_read
#print axioms InitECandidate.Solver.Input.Payload.offsets_normal
