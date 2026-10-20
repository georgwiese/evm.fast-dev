import InitECandidate.Solver.Input.MainInputCopy
import InitECandidate.Solver.Input.MainStartupTrace

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Accepted encoded lengths reach the real main suffix after input_blob,
with exact input bytes and an aggregate prefix bound from the same root run. -/
theorem copied_prefix_of_main (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (rootRun : evaluateHOLFiniteState source body = (result,target)) :
    ∃ before current final,InputReady input before ∧ InputCopied input before current ∧
      current.clock ≤ source.clock ∧ source.clock - current.clock ≤ 832 + inputPrice input ∧
      source.clock - current.clock ≤ 16778048 ∧
      evaluateHOLFiniteState current afterInput = (result,final) ∧ target = WitnessRadix.QueryBranch.restore before "inp" final := by
  have notTimeout : result ≠ some .timeOut := by
    rcases terminal with ⟨value,same⟩ | ⟨event,same⟩ <;> rw [same] <;> simp
  obtain ⟨mptMiddle,bnMiddle,evmMiddle,before,_,_,_,fork,ready,remaining⟩ := startup_trace input source target entry result terminal rootRun
  obtain ⟨funded,current,final,copied,run,restore⟩ := input_copy_prefix input before target ready bounded result remaining notTimeout
  have beforeClock := fork.forward
  have beforeCost := fork.spent
  have clock := copied.clock
  have currentForward : current.clock ≤ source.clock := by omega
  have currentCost : source.clock - current.clock ≤ 832 + inputPrice input := by omega
  have rounds := (Blob.copyRounds_fit (input.length % 2 ^ 64) bounded).2.2
  have price : inputPrice input ≤ 16777216 := by unfold inputPrice; omega
  exact ⟨before,current,final,ready,copied,currentForward,currentCost,by omega,run,restore⟩

/-- Connect the actual successful copy prefix to the challenge observation;
the endpoint's restored inp local does not change its FFI events or clock. -/
theorem source_copied_prefix (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source before current final result actualOutcome,Entry input source ∧ InputReady input before ∧ InputCopied input before current ∧
      current.clock ≤ source.clock ∧ source.clock - current.clock ≤ 832 + inputPrice input ∧ source.clock - current.clock ≤ 16778048 ∧
      evaluateHOLFiniteState current afterInput = (result,final) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome final.ffi.ioEvents := by
  obtain ⟨source,target,result,actualOutcome,entry,rootRun,classified,observation⟩ := reached input outcome events terminates
  have terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event) := by
    cases result with
    | none => cases classified
    | some result =>
      cases result with
      | returned value => exact Or.inl ⟨value,rfl⟩
      | finalFfi event => exact Or.inr ⟨event,rfl⟩
      | _ => cases classified
  obtain ⟨before,current,final,ready,copied,forward,cost,bound,run,restore⟩ := copied_prefix_of_main input source target entry bounded result terminal rootRun
  have observed : HolBehaviour.terminate outcome events = .terminate actualOutcome final.ffi.ioEvents := by
    rw [restore] at observation
    exact observation
  exact ⟨source,before,current,final,result,actualOutcome,entry,ready,copied,forward,cost,bound,run,classified,observed⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.copied_prefix_of_main
#print axioms InitECandidate.Solver.Input.Main.source_copied_prefix
