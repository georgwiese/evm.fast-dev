import InitECandidate.Solver.Input.PayloadOffsetsNormal
import InitECandidate.Solver.Input.OffsetsTrace

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual payload offset stores and count4 validator on every enclosing
non-timeout run. Rejection costs <=6 ticks; passing derives all four ranges,
ordering and fixed offset540 without assuming a full allowance or return. -/
theorem offsets_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array total : BitVec 64)
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
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source offsetBody = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 6) ∨
    (offsetWords input 0 = 540#64 ∧ (∀ position < 4,Offsets.ValidAt 540#64 total (offsetWords input) position) ∧
      ∃ (next : PanSemStateFiniteExact 64 Guest.HostMemory) (paid : Nat),paid ≤ 6 ∧ paid ≤ source.clock ∧
        next = {offsetsStored source input array with clock := source.clock - paid} ∧ Blob.HeapInput next input pointer ∧
        evaluateHOLFiniteState next offsetContinuation = (result,post)) := by
  classical
  obtain ⟨s0,s1,s2,s3,storedHeap,mapped,cells⟩ := offsets_stores source input pointer array heap arrayGlobal l0 l1 l2 l3 domain pointerAligned arrayAligned upper arrayLower arrayBefore
  let stored := offsetsStored source input array
  have actual : evaluateHOLFiniteState source offsetBody = evaluateHOLFiniteState stored (.seq guardCall offsetContinuation) := by
    rw [offset_body_shape,
      StateSteps.next_sequence source (extraStored source input array) _ _ s0 (Nat.le_refl _),
      StateSteps.next_sequence (extraStored source input array) (transactionsStored source input array) _ _ s1 (Nat.le_refl _),
      StateSteps.next_sequence (transactionsStored source input array) (withdrawalsStored source input array) _ _ s2 (Nat.le_refl _),
      StateSteps.next_sequence (withdrawalsStored source input array) stored _ _ s3 (Nat.le_refl _)]
  have args := guard_arguments_read stored array total arrayGlobal n
  have remaining : evaluateHOLFiniteState stored (.seq guardCall offsetContinuation) = (result,post) := actual.symm.trans run
  obtain ⟨next,paid,bound,enough,clock,outcome⟩ := Offsets.call_trace stored post guardArguments offsetContinuation array 540#64 total (offsetWords input) 4
    (by decide) (by decide) args code failCode exceptionShape mapped cells result remaining notTimeout
  have nextClock : next.clock = source.clock - paid := clock
  have sourceEnough : paid ≤ source.clock := enough
  rcases outcome with normal | fault
  · obtain ⟨_,nextEq,first,valid,nextRun⟩ := normal
    have nextState : next = {offsetsStored source input array with clock := source.clock - paid} := nextEq
    have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) nextEq
    have mappedDomain := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) nextEq
    have endian := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) nextEq
    have nextHeap := Blob.HeapInput.of_fields stored next input pointer memory.symm mappedDomain.symm endian.symm storedHeap
    exact Or.inr ⟨first,valid,next,paid,bound,sourceEnough,nextState,nextHeap,nextRun⟩
  · obtain ⟨error,allowed,_,same,states⟩ := fault
    refine Or.inl ⟨error,allowed,same,?_⟩
    rw [states,nextClock]
    omega

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.offsets_trace
