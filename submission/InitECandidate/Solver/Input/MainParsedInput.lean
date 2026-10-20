import InitECandidate.Solver.Input.MainDecoderCallTrace

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- From the same actual original main execution: either the complete parser
error path has the stated bound, or its literal success continuation is
reached with real SI/witness arrays after all initializers and copying. -/
theorem parsed_prefix_of_main (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (bounded : input.length%2^64≤Guest.maxInputBytes) (gas : Guest.GasLimit.declaredGasLimit input≤200000000)
    (result : Option (PanSemResultExact 64)) (terminal : (∃ value,result=some (.returned value)) ∨ ∃ event,result=some (.finalFfi event))
    (run : evaluateHOLFiniteState source body=(result,target)) :
    (source.clock-target.clock≤inputPrice input+(input.length%2^64)/4+DecoderCall.witnessLength input/2+1410) ∨
      (∃ before copied current final,InputCopied input before copied ∧ DecoderCall.DecoderReady input (DecoderSetup.entered copied input) current ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤inputPrice input+(input.length%2^64)/4+DecoderCall.witnessLength input/2+1359 ∧
        evaluateHOLFiniteState current DecoderCall.continuation=(result,final) ∧ target=QueryBranch.restore before "inp" (DecoderSetup.restoration copied input final)) := by
  have notTimeout : result≠some .timeOut := by rcases terminal with ⟨value,same⟩ | ⟨event,same⟩ <;> rw [same] <;> simp
  obtain ⟨before,copied,final,bytes,forward,cost,uniform,remaining,endpoint⟩ := decoder_prefix_of_main input source target entry bounded result terminal run
  rcases DecoderCall.decoder_call_trace input before copied final bytes bounded gas result remaining notTimeout with rejected | normal
  · have clocks : target.clock=final.clock := by rw [endpoint]; rfl
    have after := evaluateHOLFiniteState_clock_le (DecoderSetup.entered copied input) DecoderSetup.decoder
    rw [remaining] at after
    change final.clock≤(DecoderSetup.entered copied input).clock at after
    exact Or.inl (by rw [clocks]; omega)
  · obtain ⟨current,data,continued⟩ := normal
    have currentForward := data.forward
    have currentCost := data.cost
    exact Or.inr ⟨before,copied,current,final,bytes,data,by omega,by omega,continued,endpoint⟩

/-- Observed original source behavior reaches that same parsed-input state;
the actual FFI trace and challenge outcome belong to its continued run. -/
theorem source_parsed_prefix (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (bounded : input.length%2^64≤Guest.maxInputBytes) (gas : Guest.GasLimit.declaredGasLimit input≤200000000)
    (terminates : InitE.sourceBehaviour input=.terminate outcome events) :
    ∃ source target result actualOutcome,Entry input source ∧ evaluateHOLFiniteState source body=(result,target) ∧
      ((source.clock-target.clock≤inputPrice input+(input.length%2^64)/4+DecoderCall.witnessLength input/2+1410) ∨
       ∃ before copied current final,InputCopied input before copied ∧ DecoderCall.DecoderReady input (DecoderSetup.entered copied input) current ∧
         current.clock≤source.clock ∧ source.clock-current.clock≤inputPrice input+(input.length%2^64)/4+DecoderCall.witnessLength input/2+1359 ∧
         evaluateHOLFiniteState current DecoderCall.continuation=(result,final) ∧ target=QueryBranch.restore before "inp" (DecoderSetup.restoration copied input final)) ∧
      (match result with | some (.finalFfi event) => actualOutcome=HolOutcome.ffiOutcome event | some (.returned _) => actualOutcome=HolOutcome.success | _ => False) ∧
      HolBehaviour.terminate outcome events=.terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,target,result,actualOutcome,entry,run,classified,observation⟩ := reached input outcome events terminates
  have terminal : (∃ value,result=some (.returned value)) ∨ ∃ event,result=some (.finalFfi event) := by
    cases result with
    | none => cases classified
    | some result => cases result with
      | returned value => exact Or.inl ⟨value,rfl⟩
      | finalFfi event => exact Or.inr ⟨event,rfl⟩
      | _ => cases classified
  exact ⟨source,target,result,actualOutcome,entry,run,parsed_prefix_of_main input source target entry bounded gas result terminal run,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.parsed_prefix_of_main
#print axioms InitECandidate.Solver.Input.Main.source_parsed_prefix
