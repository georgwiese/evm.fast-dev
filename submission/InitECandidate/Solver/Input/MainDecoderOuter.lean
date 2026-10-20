import InitECandidate.Solver.Input.MainDecoderReject
import InitECandidate.Solver.Input.HeaderPassingEntry
import InitECandidate.Solver.Input.HeaderReady
import InitECandidate.Solver.Input.OffsetsTrace

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxHeartbeats 100000

def outerState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  Header.pairState (Header.shifted source inputPointer (input.length % 2^64)) input 2713715344#64

/-- After the leading guards pass, a real non-timeout decoder execution
runs both original offset stores and its original validator. Either its
actual SszErr10/11/12 stops within4 ticks, or it reaches the literal request
continuation with both container offsets derived from the copied input. -/
theorem outer_trace (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (passes : ¬ Rejects input)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Header.body = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64) ∧
      result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 4) ∨
    (Guest.GasLimit.le32 input 2 = 16 ∧ 16 ≤ Guest.GasLimit.le32 input 6 ∧ Guest.GasLimit.le32 input 6 ≤ input.length % 2^64 - 2 ∧
      ∃ next paid,paid ≤ 4 ∧ paid ≤ source.clock ∧ next = {outerState source input with clock := source.clock - paid} ∧
        Blob.HeapInput next input inputPointer ∧ evaluateHOLFiniteState next Header.continuation = (result,post)) := by
  have validEntry : 18 ≤ input.length % 2^64 ∧ Guest.GasLimit.byte input 0 = 21 ∧ Guest.GasLimit.byte input 1 = 1 := by
    simpa only [Rejects,not_or,not_lt,not_not] using passes
  let entered := Header.shifted source inputPointer (input.length % 2^64)
  let total := BitVec.ofNat 64 (input.length % 2^64 - 2)
  have passed := Header.passing_entry source input inputPointer environment.bytes environment.pointer environment.length validEntry.1 validEntry.2.1 validEntry.2.2
  rw [passed] at run
  have heap : Blob.HeapInput entered input inputPointer := environment.bytes
  have p : entered.locals.lookup (ofString "p") = some (.val (.word (inputPointer + 2#64))) :=
    (bind_lookup_other (QueryBranch.bind source "p" (inputPointer + 2#64)) "len" "p" _ (by decide)).trans (bind_lookup_same _ _ _)
  have n : entered.locals.lookup (ofString "len") = some (.val (.word total)) := bind_lookup_same _ _ _
  have upper : inputPointer.toNat + input.length % 2^64 + 8 ≤ 33806089496 := by
    change 2713731432 + input.length % 2^64 + 8 ≤ 33806089496
    have bound : input.length % 2^64 ≤ 134217712 := bounded
    omega
  obtain ⟨_,pairHeap,firstCell,secondCell,firstRun,secondRun,firstMapped,secondMapped⟩ := Header.pair_execute entered input inputPointer 2713715344#64 heap (by omega) p environment.offsets environment.domain
    (by decide) (by decide) upper (by decide) (by decide)
  let paired := Header.pairState entered input 2713715344#64
  have pairedClock : paired.clock = source.clock := rfl
  have restRun : evaluateHOLFiniteState paired (.seq Header.guardCall Header.continuation) = (result,post) := by
    rw [Header.after_header_shape,StateSteps.next_sequence entered (Header.firstState entered input 2713715344#64) _ _ firstRun (Nat.le_refl _),
      StateSteps.next_sequence (Header.firstState entered input 2713715344#64) paired _ _ secondRun (Nat.le_refl _)] at run
    exact run
  obtain ⟨args,mapped,cells⟩ := Header.guard_ready paired input 2713715344#64 total environment.offsets n firstMapped secondMapped firstCell secondCell
  obtain ⟨middle,paid,price,enough,middleClock,outcome⟩ := Offsets.call_trace paired post Header.guardArguments Header.continuation 2713715344#64 16#64 total (Header.offsetWords input) 2
    (by decide) (by decide) args (original_offsets_code source.code environment.code) (original_fail_code source.code environment.code) (environment.shapes .SszErr) mapped cells result restRun notTimeout
  rw [pairedClock] at enough middleClock
  rcases outcome with normal | fault
  · obtain ⟨_,middleEq,first,valid,remaining⟩ := normal
    have rawSmall : Guest.GasLimit.le32 input 2 < 2^64 := by
      have bound := HostGas.le32_lt input 2
      rw [HostGas.le32_eq input 2 (by decide)] at bound
      omega
    have number := congrArg BitVec.toNat first
    change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 2)).toNat = 16 at number
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt rawSmall] at number
    have secondSmall : Guest.GasLimit.le32 input 6 < 2^64 := by
      have bound := HostGas.le32_lt input 6
      rw [HostGas.le32_eq input 6 (by decide)] at bound
      omega
    have encodedSecond : (Header.secondWord input).toNat = Guest.GasLimit.le32 input 6 := by
      rw [Header.secondWord,BitVec.toNat_ofNat,Nat.mod_eq_of_lt secondSmall]
    have secondValid := valid 1 (by decide)
    change 16 ≤ (Header.secondWord input).toNat ∧ (Header.secondWord input).toNat ≤ total.toNat ∧ _ at secondValid
    rw [encodedSecond] at secondValid
    have encodedTotal : total.toNat = input.length % 2^64 - 2 := by
      have small : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    rw [encodedTotal] at secondValid
    have actualNext : middle = {outerState source input with clock := source.clock - paid} := middleEq
    have memory : paired.memory = middle.memory := by
      have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) middleEq
      exact projected.symm
    have domain : paired.memaddrs = middle.memaddrs := by
      have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) middleEq
      exact projected.symm
    have endian : paired.be = middle.be := by
      have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) middleEq
      exact projected.symm
    have nextHeap := Blob.HeapInput.of_fields paired middle input inputPointer memory domain endian pairHeap
    exact Or.inr ⟨number,secondValid.1,secondValid.2.1,middle,paid,price,enough,actualNext,nextHeap,remaining⟩
  · obtain ⟨error,allowed,_,same,states⟩ := fault
    refine Or.inl ⟨error,allowed,same,?_⟩
    rw [states,middleClock]
    omega

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.outer_trace
