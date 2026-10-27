import InitECandidate.Solver.Input.HeaderReady
import InitECandidate.Solver.Input.OffsetsTrace

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 20000

/-- Real returning execution funds its actual first validator cost. Both
workspace stores and the validator retain the copied input bytes. -/
theorem after_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array total : BitVec 64) (heap : Blob.HeapInput source input pointer) (inside : 10 ≤ input.length % 2^64)
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word (pointer + 2#64))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (totalLocal : source.locals.lookup (ofString "len") = some (.val (.word total)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat % 8 = 0) (arrayAligned : array.toNat % 8 = 0)
    (upper : pointer.toNat + input.length % 2^64 + 8 ≤ 33806089496)
    (arrayLower : 2701131776 ≤ array.toNat) (arrayBefore : array.toNat + 16 ≤ pointer.toNat)
    (code : source.code.lookup (ofString "ssz_check_offsets") = some (Offsets.formals, Offsets.body, .one))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals, SszFail.body, .one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterHeader = (some (.returned value), post)) :
    ∃ next paid, paid ≤ 4 ∧ paid ≤ source.clock ∧
      next = {pairState source input array with clock := source.clock - paid} ∧
      Blob.HeapInput next input pointer ∧ evaluateHOLFiniteState next continuation = (some (.returned value), post) := by
  obtain ⟨pairRun, pairHeap, firstCell, secondCell, firstRun, secondRun, firstMapped, secondMapped⟩ :=
    pair_execute source input pointer array heap inside pointerLocal arrayGlobal domain pointerAligned arrayAligned upper arrayLower arrayBefore
  let paired := pairState source input array
  have actualPrefix : evaluateHOLFiniteState source afterHeader = evaluateHOLFiniteState paired (.seq guardCall continuation) := by
    rw [after_header_shape, WitnessRadix.StateSteps.next_sequence source (firstState source input array) _ _ firstRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence (firstState source input array) paired _ _ secondRun (Nat.le_refl _)]
  have rest : evaluateHOLFiniteState paired (.seq guardCall continuation) = (some (.returned value), post) := actualPrefix.symm.trans run
  obtain ⟨args, mapped, cells⟩ := guard_ready paired input array total arrayGlobal totalLocal firstMapped secondMapped firstCell secondCell
  obtain ⟨next, paid, price, enough, clock, outcome⟩ := Offsets.call_trace paired post guardArguments continuation
    array 16#64 total (offsetWords input) 2 (by decide) (by decide) args code failCode exceptionShape
    mapped cells (some (.returned value)) rest (by simp)
  rcases outcome with normal | fault
  · obtain ⟨guardRun, nextEq, firstWord, valid, remaining⟩ := normal
    refine ⟨next, paid, price, enough, nextEq, ?_, remaining⟩
    have memory : paired.memory = next.memory := (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) nextEq).symm
    have domain : paired.memaddrs = next.memaddrs := (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) nextEq).symm
    have endian : paired.be = next.be := (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) nextEq).symm
    exact Blob.HeapInput.of_fields paired next input pointer memory domain endian pairHeap
  · obtain ⟨error, allowed, guardRun, impossible, stopped⟩ := fault
    cases impossible

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.after_trace
