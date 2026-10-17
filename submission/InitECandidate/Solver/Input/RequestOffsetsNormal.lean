import InitECandidate.Solver.Input.RequestOffsetsSetup

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

set_option maxHeartbeats 20000

theorem guard_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array total : BitVec 64)
    (a : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (n : source.locals.lookup (ofString "nlen")=some (.val (.word total))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) guardArguments=
      some (Offsets.arguments array 44#64 total 3) := by
  classical
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,guardArguments,Offsets.arguments,Header.offsets,localVar,a,n]

theorem state_from_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (paid : Nat)
    (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid})
    (locals : target.locals=source.locals) : target={source with clock:=source.clock-paid} := by
  have full:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=target.locals}) frame
  have allFields : target={{source with clock:=source.clock-paid} with locals:=target.locals} := by
    simpa only [emptyLocalsHOLFinite] using full
  rw [locals] at allFields
  exact allFields

/-- A normal return of the actual request tail must pass the genuine offset
validator. All rejected arrays are covered and cannot resume the continuation. -/
theorem offsets_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array total : BitVec 64) (heap : Blob.HeapInput source input pointer) (inside : 62≤input.length%2^64)
    (np : source.locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))))
    (nlen : source.locals.lookup (ofString "nlen")=some (.val (.word total)))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat)
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 5≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source requestBody=(some (.returned value),post)) :
    requestWords input 0=44#64 ∧ (∀ position<3,Offsets.ValidAt 44#64 total (requestWords input) position) ∧
      ∃ next innerPost paid,paid≤5 ∧ next={offsetsStored source input array with clock:=source.clock-paid} ∧
        Blob.HeapInput next input pointer ∧ evaluateHOLFiniteState next continuation=(some (.returned value),innerPost) := by
  classical
  obtain ⟨setup,storedHeap,mapped,cells⟩:=offsets_setup source input pointer array heap inside np arrayGlobal domain pointerAligned arrayAligned upper arrayLower arrayBefore
  let stored:=offsetsStored source input array
  have actual:=WitnessRadix.ProgramPrefix.execute setup (.seq guardCall continuation)
  rw [←offset_actions_shape] at actual
  have storedN : stored.locals.lookup (ofString "nlen")=some (.val (.word total)) :=
    (bind_lookup_other (offsetSecond source input) "o_rq" "nlen" _ (by decide)).trans
      ((bind_lookup_other (offsetFirst source input) "o_vh" "nlen" _ (by decide)).trans
        ((bind_lookup_other source "o_pl" "nlen" _ (by decide)).trans nlen))
  have args:=guard_arguments_read stored array total arrayGlobal storedN
  obtain ⟨result,target,paid,guardRun,bound,frame,outcome⟩:=Offsets.call_execute stored guardArguments array 44#64 total (requestWords input) 3
    (by decide) (by decide) args code failCode exceptionShape mapped cells enough
  have clock : target.clock=source.clock-paid := by
    have h:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.clock) frame
    exact h
  have tailResult : (evaluateHOLFiniteState stored (.seq guardCall continuation)).1=some (.returned value) := by
    have h:=congrArg Prod.fst (actual.symm.trans run)
    exact h
  rcases outcome with normal|fault
  · have guardNone : evaluateHOLFiniteState stored guardCall=(none,target) := by simpa only [normal.1,guardCall] using guardRun
    have continued:=WitnessRadix.StateSteps.next_sequence stored target guardCall continuation guardNone (by change target.clock≤source.clock; rw [clock]; omega)
    rw [continued] at tailResult
    have targetEq:=state_from_frame stored target paid frame normal.2.2.1
    have storedClock : stored.clock=source.clock := rfl
    rw [storedClock] at targetEq
    have memEq:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memory) frame
    have domainEq:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memaddrs) frame
    have endianEq:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.be) frame
    have heapAfter:=Blob.HeapInput.of_fields stored target input pointer memEq.symm domainEq.symm endianEq.symm storedHeap
    refine ⟨normal.2.1,normal.2.2.2,target,(evaluateHOLFiniteState target continuation).2,paid,bound,targetEq,heapAfter,?_⟩
    exact Prod.ext tailResult rfl
  · obtain ⟨error,allowed,resultEq⟩:=fault
    have guardFault : evaluateHOLFiniteState stored guardCall=
        (some (.exception (ofString "SszErr") (.val (.word error))),target) := by simpa only [resultEq,guardCall] using guardRun
    have stopped:=WitnessRadix.StateSteps.stopped_sequence stored target guardCall continuation
      (.exception (ofString "SszErr") (.val (.word error))) guardFault (by change target.clock≤source.clock; rw [clock]; omega)
    rw [stopped] at tailResult
    cases tailResult

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.offsets_normal

#print axioms InitECandidate.Solver.Input.Request.guard_arguments_read

#print axioms InitECandidate.Solver.Input.Request.state_from_frame
