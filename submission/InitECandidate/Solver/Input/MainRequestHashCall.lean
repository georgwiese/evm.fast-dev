import InitECandidate.Solver.Input.RequestRootHashProgram
import InitECandidate.Solver.Input.NonTimeoutSequenceCall

namespace InitECandidate.Solver.Input.Main.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The literal original main request-root call reaches its real callee with
actual SI/root arguments. Its call tick and callee non-timeout execution come
from the same observed main continuation; no successful hash is assumed. -/
theorem call_trace (input : Guest.InputBlob) (before copiedSource current post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (entered current root) afterRoot=(result,post)) (notTimeout : result≠some .timeOut) :
    ∃ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (bodyResult : Option (PanSemResultExact 64)) (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory),
      lookupCodeHOLFinite (entered current root).code.lookup (ofString "htr_new_payload_request") (RequestRootHash.values (RequestPrefix.cursor input) root)=some (RequestRootHash.body,callee,.one) ∧
      callee.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))) ∧ callee.lookup (ofString "out")=some (.val (.word root)) ∧
      1≤(entered current root).clock ∧ bodyResult≠some .timeOut ∧ evaluateHOLFiniteState (callEntryStateHOLFinite (entered current root) callee) RequestRootHash.body=(bodyResult,bodyPost) := by
  let caller := entered current root
  have context := DecoderSetup.entered_context copiedSource input
  have callerCode : (DecoderSetup.entered copiedSource input).code=copiedSource.code := by have h := congrArg PanSemStateFiniteExact.code context; exact h
  have code : caller.code=copiedSource.code := actual.code.trans callerCode
  have installed : OriginalCode.Installed caller.code := code.symm ▸ copied.code
  have args := RequestRootHash.main_arguments input (DecoderSetup.entered copiedSource input) current root actual
  obtain ⟨callee,called,si,out⟩ := RequestRootHash.environment caller.code.lookup (RequestPrefix.cursor input) root (RequestRootHash.original_code caller.code installed)
  rw [original_shape.2,call] at run
  obtain ⟨funded,nonTimeout⟩ := sequence_call_non_timeout caller post (some (none,none)) (ofString "htr_new_payload_request") arguments
    (RequestRootHash.values (RequestPrefix.cursor input) root) RequestRootHash.body continuation callee .one args called result run notTimeout
  let entry := callEntryStateHOLFinite caller callee
  exact ⟨callee,(evaluateHOLFiniteState entry RequestRootHash.body).1,(evaluateHOLFiniteState entry RequestRootHash.body).2,called,si,out,funded,nonTimeout,rfl⟩

end InitECandidate.Solver.Input.Main.RequestHash

#print axioms InitECandidate.Solver.Input.Main.RequestHash.call_trace
