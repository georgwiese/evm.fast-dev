import InitECandidate.Solver.Input.HeaderReady

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normal return from the entire remaining decoder entails normal passage
through its actual first offset stores/validator, and exposes the real next
continuation. Rejected arrays cannot resume into that continuation. -/
theorem after_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array total : BitVec 64) (heap : Blob.HeapInput source input pointer) (inside : 10≤input.length%2^64)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+16≤pointer.toNat)
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 4≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterHeader=(some (.returned value),post)) :
    Guest.GasLimit.le32 input 2=16 ∧ 16≤Guest.GasLimit.le32 input 6 ∧ Guest.GasLimit.le32 input 6≤total.toNat ∧
      ∃ next paid,paid≤4 ∧ next={pairState source input array with clock:=source.clock-paid} ∧
        Blob.HeapInput next input pointer ∧ evaluateHOLFiniteState next continuation=(some (.returned value),post) := by
  classical
  obtain ⟨pairRun,pairHeap,firstCell,secondCell,firstRun,secondRun,firstMapped,secondMapped⟩:=
    pair_execute source input pointer array heap inside pointerLocal arrayGlobal domain pointerAligned arrayAligned upper arrayLower arrayBefore
  let paired:=pairState source input array
  have actualPrefix : evaluateHOLFiniteState source afterHeader=evaluateHOLFiniteState paired (.seq guardCall continuation) := by
    rw [after_header_shape,WitnessRadix.StateSteps.next_sequence source (firstState source input array) _ _ firstRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence (firstState source input array) paired _ _ secondRun (Nat.le_refl _)]
  have restRun : evaluateHOLFiniteState paired (.seq guardCall continuation)=(some (.returned value),post) := actualPrefix.symm.trans run
  obtain ⟨args,mapped,cells⟩:=guard_ready paired input array total arrayGlobal totalLocal
    (by simpa [paired,pairState,firstState] using firstMapped) (by simpa [paired,pairState,firstState] using secondMapped) firstCell secondCell
  obtain ⟨result,target,paid,guardRun,bound,frame,outcome⟩:=Offsets.call_execute paired guardArguments array 16#64 total (offsetWords input) 2
    (by decide) (by decide) args code failCode exceptionShape mapped cells enough
  have clock : target.clock=source.clock-paid := by
    have h:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.clock) frame
    exact h
  rcases outcome with normal|fault
  · have guardNone : evaluateHOLFiniteState paired guardCall=(none,target) := by simpa only [normal.1,guardCall] using guardRun
    have prefixRun : evaluateHOLFiniteState source prefixCode=(none,target) := by
      rw [prefixCode,WitnessRadix.StateSteps.next_sequence source (firstState source input array) _ _ firstRun (Nat.le_refl _),
        WitnessRadix.StateSteps.next_sequence (firstState source input array) paired _ _ secondRun (Nat.le_refl _)]
      exact guardNone
    obtain ⟨first,lower,upperWitness,heapAfter,paid',bound',postEq⟩:=guard_normal source target input pointer array total heap inside
      pointerLocal arrayGlobal totalLocal domain pointerAligned arrayAligned upper arrayLower arrayBefore code failCode exceptionShape enough prefixRun
    have continued:=WitnessRadix.StateSteps.next_sequence paired target guardCall continuation guardNone (by change target.clock≤source.clock; rw [clock]; omega)
    rw [continued] at restRun
    exact ⟨first,lower,upperWitness,target,paid',bound',postEq,heapAfter,restRun⟩
  · obtain ⟨error,allowed,resultEq⟩:=fault
    have guardFault : evaluateHOLFiniteState paired guardCall=
        (some (.exception (ofString "SszErr") (.val (.word error))),target) := by simpa only [resultEq,guardCall] using guardRun
    have stopped:=WitnessRadix.StateSteps.stopped_sequence paired target guardCall continuation
      (.exception (ofString "SszErr") (.val (.word error))) guardFault (by change target.clock≤source.clock; rw [clock]; omega)
    rw [stopped] at restRun
    have impossible:=congrArg Prod.fst restRun
    cases impossible

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.after_normal
