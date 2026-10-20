import InitECandidate.Solver.Input.MainDecoderRejectedBound

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Whole original main on a bounded input rejected by its initial decoder
length/schema guards. Startup, actual input copying, output setup and the
complete original catch handler are all included in the same actual run. -/
theorem rejected_main_cost (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes) (rejects : DecoderCall.Rejects input)
    (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (run : evaluateHOLFiniteState source body = (result,target)) :
    source.clock - target.clock ≤ 889 + inputPrice input ∧ source.clock - target.clock ≤ 16778105 := by
  obtain ⟨before,current,final,copied,forward,prefixCost,prefixBound,remaining,restored⟩ := decoder_prefix_of_main input source target entry bounded result terminal run
  have suffix := DecoderCall.rejected_cost input before current copied bounded rejects
  have finalClock := evaluateHOLFiniteState_clock_le (DecoderSetup.entered current input) DecoderSetup.decoder
  rw [remaining] at suffix finalClock
  change (DecoderSetup.entered current input).clock - final.clock ≤ 53 at suffix
  change final.clock ≤ (DecoderSetup.entered current input).clock at finalClock
  have finalEq : target.clock = final.clock := by rw [restored]; rfl
  rw [finalEq]
  exact ⟨by omega,by omega⟩

/-- The same branch bound for the challenge's actual terminating source
observation, preserving its original main run and complete FFI trace. -/
theorem source_rejected_bound (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes) (rejects : DecoderCall.Rejects input)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source target result actualOutcome,Entry input source ∧ evaluateHOLFiniteState source body = (result,target) ∧
      source.clock - target.clock ≤ 889 + inputPrice input ∧ source.clock - target.clock ≤ 16778105 ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧ HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,target,result,actualOutcome,entry,run,classified,observation⟩ := reached input outcome events terminates
  have terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event) := by
    cases result with
    | none => cases classified
    | some result =>
      cases result with
      | returned value => exact Or.inl ⟨value,rfl⟩
      | finalFfi event => exact Or.inr ⟨event,rfl⟩
      | _ => cases classified
  obtain ⟨cost,bound⟩ := rejected_main_cost input source target entry bounded rejects result terminal run
  exact ⟨source,target,result,actualOutcome,entry,run,cost,bound,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.rejected_main_cost
#print axioms InitECandidate.Solver.Input.Main.source_rejected_bound
