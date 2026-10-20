import InitECandidate.Solver.Input.MainDecoderEntry

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def Rejects (input : Guest.InputBlob) : Prop := input.length % 2 ^ 64 < 18 ∨ Guest.GasLimit.byte input 0 ≠ 21 ∨ Guest.GasLimit.byte input 1 ≠ 1
def rejectionCode (input : Guest.InputBlob) : BitVec 64 :=
  if input.length % 2 ^ 64 < 2 then 1#64 else if Guest.GasLimit.byte input 0 ≠ 21 ∨ Guest.GasLimit.byte input 1 ≠ 1 then 2#64 else 80#64
def handlerState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  QueryBranch.bind {DecoderSetup.entered source input with clock := (DecoderSetup.entered source input).clock - 2} "err_code" (rejectionCode input)

theorem program_shape : program = .call (some (some (.local,ofString "si"),some (ofString "SszErr",ofString "err_code",handler)))
    (ofString "decode_stateless_input") arguments := by
  unfold program
  rw [original_shape]

theorem rejected_body (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (rejects : Rejects input) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source Header.body = (some (.exception (ofString "SszErr") (.val (.word (rejectionCode input)))),emptyLocalsHOLFinite {source with clock := source.clock - 1}) := by
  have shape : source.eshapes.lookup (ofString "SszErr") = some .one := environment.shapes .SszErr
  have actual := Header.entry_execute source input inputPointer environment.bytes environment.pointer environment.length (original_fail_code source.code environment.code) shape enough
  rw [actual]
  unfold rejectionCode
  by_cases short : input.length % 2 ^ 64 < 2
  · simp only [if_pos short]
  · simp only [if_neg short]
    by_cases wrong : Guest.GasLimit.byte input 0 ≠ 21 ∨ Guest.GasLimit.byte input 1 ≠ 1
    · simp only [if_pos wrong]
    · have small : input.length % 2 ^ 64 < 18 := by rcases rejects with small | first | second; exact small; exact False.elim (wrong (Or.inl first)); exact False.elim (wrong (Or.inr second))
      simp only [if_neg wrong,if_pos small]

private theorem handler_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (word : BitVec 64) :
    setVarHOLFinite (ofString "err_code") (.val (.word word))
      {emptyLocalsHOLFinite {callEntryStateHOLFinite source callee with clock := (callEntryStateHOLFinite source callee).clock - 1} with locals := source.locals} =
      QueryBranch.bind {source with clock := source.clock - 2} "err_code" word := by
  have clock : source.clock - 1 - 1 = source.clock - 2 := by omega
  simp only [callEntryStateHOLFinite,emptyLocalsHOLFinite,QueryBranch.bind,clock]

/-- The real main decoder caller takes its actual SszErr handler on each
early length/schema rejection, with the exact error code and two paid calls. -/
theorem reject_to_handler (input : Guest.InputBlob) (before source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes)
    (rejects : Rejects input) (enough : 2 ≤ (DecoderSetup.entered source input).clock) :
    evaluateHOLFiniteState (DecoderSetup.entered source input) program = evaluateHOLFiniteState (handlerState source input) handler := by
  obtain ⟨callee,args,called,environment⟩ := entry_data input before source copied bounded
  let caller := DecoderSetup.entered source input
  let entry := callEntryStateHOLFinite caller callee
  have callerEnough : 2 ≤ caller.clock := enough
  have run := rejected_body input entry environment rejects (by change 1 ≤ caller.clock - 1; omega)
  have shape : caller.eshapes.lookup (ofString "SszErr") = some .one := environment.shapes .SszErr
  have err : caller.locals.lookup (ofString "err_code") = some (.val (.word 0#64)) := (DecoderSetup.entered_bindings source input).2.2.2.2
  have finiteValid : isValidValueHOLFinite caller .local (ofString "err_code") (.val (.word (rejectionCode input))) = true := by
    simp [isValidValueHOLFinite,lookupKvarHOLFinite,err,shapeOfHOLExact,shapeEqHOL]
  have valid : isValidValueHOLExact caller.toExact .local (ofString "err_code") (.val (.word (rejectionCode input))) = true := by
    simpa only [isValidValueHOLFinite_eq] using finiteValid
  have actual := evaluateHOLFiniteState_call_matched_exception_handler caller (some (.local,ofString "si")) (ofString "SszErr") (ofString "err_code")
    (ofString "decode_stateless_input") handler Header.body arguments (values inputPointer (input.length % 2 ^ 64)) callee .one (.val (.word (rejectionCode input)))
    (emptyLocalsHOLFinite {entry with clock := entry.clock - 1}) .one args called (by change caller.clock ≠ 0; omega) run shape (by simp [shapeOfHOLExact,shapeEqHOL]) valid
  rw [handler_frame caller callee (rejectionCode input)] at actual
  rw [program_shape]
  exact actual

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.program_shape
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.rejected_body
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.reject_to_handler
