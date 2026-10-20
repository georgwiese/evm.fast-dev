import InitECandidate.Solver.Input.MainDecoderReject
import InitECandidate.Solver.Input.NonTimeoutSequenceCall

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The same actual main continuation derives its decoder caller funding and
a non-timeout run of the original callee, with all current entry facts.
No decoder return, schema or gas validity is assumed. -/
theorem actual_body (input : Guest.InputBlob) (before source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before source) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState (DecoderSetup.entered source input) DecoderSetup.decoder = (result,target)) (notTimeout : result ≠ some .timeOut) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      evalListHOLFinite (DecoderSetup.entered source input) (h := fun address => Classical.propDecidable ((DecoderSetup.entered source input).memaddrs address)) arguments = some (values inputPointer (input.length % 2^64)) ∧
      lookupCodeHOLFinite (DecoderSetup.entered source input).code.lookup (ofString "decode_stateless_input") (values inputPointer (input.length % 2^64)) = some (Header.body,callee,.one) ∧
      Environment input (callEntryStateHOLFinite (DecoderSetup.entered source input) callee) ∧
      1 ≤ (DecoderSetup.entered source input).clock ∧
      (evaluateHOLFiniteState (callEntryStateHOLFinite (DecoderSetup.entered source input) callee) Header.body).1 ≠ some .timeOut := by
  obtain ⟨callee,args,called,environment⟩ := entry_data input before source copied bounded
  rw [original_shape] at run
  obtain ⟨funded,calleeRun⟩ := sequence_call_non_timeout (DecoderSetup.entered source input) target
    (some (some (.local,ofString "si"),some (ofString "SszErr",ofString "err_code",handler))) (ofString "decode_stateless_input") arguments (values inputPointer (input.length % 2^64))
    Header.body continuation callee .one args called result run notTimeout
  exact ⟨callee,args,called,environment,funded,calleeRun⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.actual_body
