import InitECandidate.Solver.Input.RequestOffsetsNormal
import InitECandidate.Solver.Input.OffsetsTrace

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open WitnessRadix.ProgramPrefix
set_option maxHeartbeats 100000

/-- All-outcome request-offset prefix for an actual enclosing non-timeout
run. Each current offset is read from the copied bytes and stored into the
real workspace. The actual validator cost is derived, with no funding or
successful payload/normal-return premise. -/
theorem offsets_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source requestBody = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 5) ∨
    (requestWords input 0 = 44#64 ∧ (∀ position < 3,Offsets.ValidAt 44#64 total (requestWords input) position) ∧
      ∃ (next innerPost : PanSemStateFiniteExact 64 Guest.HostMemory) (paid : Nat),paid ≤ 5 ∧ paid ≤ source.clock ∧
        next = {offsetsStored source input array with clock := source.clock - paid} ∧ Blob.HeapInput next input pointer ∧
        evaluateHOLFiniteState next continuation = (result,innerPost) ∧ post = restoreOffsets source input innerPost) := by
  classical
  obtain ⟨setup,storedHeap,mapped,cells⟩ := offsets_setup source input pointer array heap inside np arrayGlobal domain pointerAligned arrayAligned upper arrayLower arrayBefore
  let stored := offsetsStored source input array
  have actual := WitnessRadix.ProgramPrefix.execute setup (.seq guardCall continuation)
  rw [← offset_actions_shape] at actual
  have completeRun := actual.symm.trans run
  let innerPost := (evaluateHOLFiniteState stored (.seq guardCall continuation)).2
  have observed := congrArg Prod.fst completeRun
  have innerRun : evaluateHOLFiniteState stored (.seq guardCall continuation) = (result,innerPost) := Prod.ext observed rfl
  have restored : post = restoreOffsets source input innerPost := (congrArg Prod.snd completeRun).symm
  have preserved := WitnessRadix.ProgramPrefix.restoration_frame setup innerPost
  have postClock : post.clock = innerPost.clock := by
    rw [restored]
    have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) preserved
    exact projected
  have storedN : stored.locals.lookup (ofString "nlen") = some (.val (.word total)) :=
    (bind_lookup_other (offsetSecond source input) "o_rq" "nlen" _ (by decide)).trans
      ((bind_lookup_other (offsetFirst source input) "o_vh" "nlen" _ (by decide)).trans
        ((bind_lookup_other source "o_pl" "nlen" _ (by decide)).trans nlen))
  have args := guard_arguments_read stored array total arrayGlobal storedN
  obtain ⟨next,paid,bound,enough,clock,outcome⟩ := Offsets.call_trace stored innerPost guardArguments continuation array 44#64 total (requestWords input) 3
    (by decide) (by decide) args code failCode exceptionShape mapped cells result innerRun notTimeout
  have nextClock : next.clock = source.clock - paid := clock
  have sourceEnough : paid ≤ source.clock := enough
  rcases outcome with normal | fault
  · obtain ⟨_,nextEq,first,valid,remaining⟩ := normal
    have nextState : next = {offsetsStored source input array with clock := source.clock - paid} := nextEq
    have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) nextEq
    have mappedDomain := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) nextEq
    have endian := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) nextEq
    have nextHeap := Blob.HeapInput.of_fields stored next input pointer memory.symm mappedDomain.symm endian.symm storedHeap
    exact Or.inr ⟨first,valid,next,innerPost,paid,bound,sourceEnough,nextState,nextHeap,remaining,restored⟩
  · obtain ⟨error,allowed,_,same,states⟩ := fault
    refine Or.inl ⟨error,allowed,same,?_⟩
    rw [postClock,states,nextClock]
    omega

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.offsets_trace
