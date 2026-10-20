import InitECandidate.Solver.Input.MainDecoderFields
import InitECandidate.Solver.Input.MainInputPrefix
import InitECandidate.Solver.Input.TerminatingProgramPrefix

namespace InitECandidate.Solver.Input.Main.DecoderSetup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- The original continuation itself supplies the four setup ticks; every
allocation, zero call and declaration is executed from current entry facts. -/
theorem setup_prefix (input : Guest.InputBlob) (before source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterInput = (result,target)) (notTimeout : result ≠ some .timeOut) :
    4 ≤ source.clock ∧ ∃ final,evaluateHOLFiniteState (entered source input) decoder = (result,final) ∧ target = restoration source input final := by
  have padded := setup input {source with clock := source.clock + 4} copied.code copied.heap copied.domain bounded (by change 4 ≤ source.clock + 4; omega)
  rw [original_shape] at run
  have enough := terminating_program_prefix source target (entered {source with clock := source.clock + 4} input) actions decoder
    (restoration {source with clock := source.clock + 4} input) 4 padded result run notTimeout
  have funded : 4 ≤ source.clock := by change 4 ≤ source.clock + 4 - 4 at enough; omega
  have actual := setup input source copied.code copied.heap copied.domain bounded funded
  rw [ProgramPrefix.execute actual decoder] at run
  let final := (evaluateHOLFiniteState (entered source input) decoder).2
  have observed : (evaluateHOLFiniteState (entered source input) decoder).1 = result := congrArg Prod.fst run
  exact ⟨funded,final,Prod.ext observed rfl,(congrArg Prod.snd run).symm⟩

end InitECandidate.Solver.Input.Main.DecoderSetup

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- From the same original main run, all startup, actual input copying and
output-buffer setup reach the real decoder/catch-handler suffix. -/
theorem decoder_prefix_of_main (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (rootRun : evaluateHOLFiniteState source body = (result,target)) :
    ∃ before current final,InputCopied input before current ∧
      (DecoderSetup.entered current input).clock ≤ source.clock ∧ source.clock - (DecoderSetup.entered current input).clock ≤ 836 + inputPrice input ∧
      source.clock - (DecoderSetup.entered current input).clock ≤ 16778052 ∧
      evaluateHOLFiniteState (DecoderSetup.entered current input) DecoderSetup.decoder = (result,final) ∧
      target = QueryBranch.restore before "inp" (DecoderSetup.restoration current input final) := by
  have notTimeout : result ≠ some .timeOut := by
    rcases terminal with ⟨value,same⟩ | ⟨event,same⟩ <;> rw [same] <;> simp
  obtain ⟨before,current,copyFinal,_,copied,forward,cost,bound,copyRun,restoreInput⟩ := copied_prefix_of_main input source target entry bounded result terminal rootRun
  obtain ⟨funded,final,run,restoreSetup⟩ := DecoderSetup.setup_prefix input before current copyFinal copied bounded result copyRun notTimeout
  have clock := DecoderSetup.entered_clock current input
  have restored : target = QueryBranch.restore before "inp" (DecoderSetup.restoration current input final) := by rw [restoreInput,restoreSetup]
  exact ⟨before,current,final,copied,by omega,by omega,by omega,run,restored⟩

/-- The reached decoder suffix carries the same challenge outcome and complete
FFI trace as the original source behavior. -/
theorem source_decoder_prefix (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source before current final result actualOutcome,Entry input source ∧ InputCopied input before current ∧
      (DecoderSetup.entered current input).clock ≤ source.clock ∧ source.clock - (DecoderSetup.entered current input).clock ≤ 836 + inputPrice input ∧
      source.clock - (DecoderSetup.entered current input).clock ≤ 16778052 ∧
      evaluateHOLFiniteState (DecoderSetup.entered current input) DecoderSetup.decoder = (result,final) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧ HolBehaviour.terminate outcome events = .terminate actualOutcome final.ffi.ioEvents := by
  obtain ⟨source,target,result,actualOutcome,entry,rootRun,classified,observation⟩ := reached input outcome events terminates
  have terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event) := by
    cases result with
    | none => cases classified
    | some result =>
      cases result with
      | returned value => exact Or.inl ⟨value,rfl⟩
      | finalFfi event => exact Or.inr ⟨event,rfl⟩
      | _ => cases classified
  obtain ⟨before,current,final,copied,forward,cost,bound,run,restore⟩ := decoder_prefix_of_main input source target entry bounded result terminal rootRun
  have observed : HolBehaviour.terminate outcome events = .terminate actualOutcome final.ffi.ioEvents := by
    rw [restore] at observation
    exact observation
  exact ⟨source,before,current,final,result,actualOutcome,entry,copied,forward,cost,bound,run,classified,observed⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.setup_prefix
#print axioms InitECandidate.Solver.Input.Main.decoder_prefix_of_main

#print axioms InitECandidate.Solver.Input.Main.source_decoder_prefix
