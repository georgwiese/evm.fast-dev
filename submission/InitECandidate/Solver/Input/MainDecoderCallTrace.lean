import InitECandidate.Solver.Input.MainDecoderTrace
import InitECandidate.Solver.Input.ParserGlobalsFull
import InitECandidate.Solver.Input.MainDecoderActual
import InitECandidate.Solver.Input.MainErrorEntry
import InitECandidate.Solver.Input.MainErrorStopped

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

structure DecoderReady (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  locals : current.locals=caller.locals.update (ofString "si",.val (.word (RequestPrefix.cursor input)))
  si : current.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input)))
  decoded : WitnessDecoded input current
  image : Payload.Image current input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
  records : VarList.Records current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input)
  hashes : RequestHashImage input current
  requests : RequestsDecoded input current
  ffi : current.ffi=caller.ffi
  globals : ∀ key,key≠ofString "heap_ptr" → current.globals.lookup key=caller.globals.lookup key
  code : current.code=caller.code
  domain : current.memaddrs=caller.memaddrs
  exceptions : current.eshapes=caller.eshapes
  endian : current.be=caller.be
  forward : current.clock≤caller.clock
  cost : caller.clock-current.clock≤(input.length%2^64)/4+witnessLength input/2+523
  payloadLayout : Payload.Layout input (PayloadPrefix.length input)
  layout : RequestLayout input

/-- The original main decoder call/catch either terminates in its actual
parser-error handler or reaches the literal success continuation with actual
SI/records. Caller funding, real handler state and all costs are derived. -/
theorem decoder_call_trace (input : Guest.InputBlob) (before source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before source) (bounded : input.length%2^64≤Guest.maxInputBytes) (gas : Guest.GasLimit.declaredGasLimit input≤200000000)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (DecoderSetup.entered source input) DecoderSetup.decoder=(result,target)) (notTimeout : result≠some .timeOut) :
    ((DecoderSetup.entered source input).clock-target.clock≤(input.length%2^64)/4+witnessLength input/2+574) ∨
    (∃ current,DecoderReady input (DecoderSetup.entered source input) current ∧ evaluateHOLFiniteState current continuation=(result,target)) := by
  let caller := DecoderSetup.entered source input
  obtain ⟨callee,args,called,environment,funded,bodyNonTimeout⟩ := actual_body input before source target copied bounded result run notTimeout
  have callerFunded : 1≤caller.clock := funded
  let entry := callEntryStateHOLFinite caller callee
  let bodyResult := (evaluateHOLFiniteState entry Header.body).1
  let bodyPost := (evaluateHOLFiniteState entry Header.body).2
  have bodyRun : evaluateHOLFiniteState entry Header.body=(bodyResult,bodyPost) := rfl
  obtain ⟨cost,outcome⟩ := decoder_trace input entry bodyPost environment bounded gas bodyResult bodyRun bodyNonTimeout
  have bodyForward : bodyPost.clock≤caller.clock-1 := evaluateHOLFiniteState_clock_le entry Header.body
  have fields := evaluation_fields entry bodyPost Header.body bodyResult bodyRun
  have callerSi : caller.locals.lookup (ofString "si")=some (.val (.word 0#64)) := (DecoderSetup.entered_bindings source input).2.2.2.1
  have callerErr : caller.locals.lookup (ofString "err_code")=some (.val (.word 0#64)) := (DecoderSetup.entered_bindings source input).2.2.2.2
  rcases outcome with rejected | normal
  · obtain ⟨error,same⟩ := rejected
    have actualBody : evaluateHOLFiniteState entry Header.body=(some (.exception (ofString "SszErr") (.val (.word error))),bodyPost) := by rw [bodyRun,same]
    have validFinite : isValidValueHOLFinite caller .local (ofString "err_code") (.val (.word error))=true := by
      simp [isValidValueHOLFinite,lookupKvarHOLFinite,callerErr,shapeOfHOLExact,shapeEqHOL]
    have valid : isValidValueHOLExact caller.toExact .local (ofString "err_code") (.val (.word error))=true := by simpa only [isValidValueHOLFinite_eq] using validFinite
    have caught := evaluateHOLFiniteState_call_matched_exception_handler caller (some (.local,ofString "si")) (ofString "SszErr") (ofString "err_code")
      (ofString "decode_stateless_input") handler Header.body arguments (values inputPointer (input.length%2^64)) callee .one (.val (.word error)) bodyPost .one args called (by omega) actualBody (environment.shapes .SszErr) (by simp [shapeOfHOLExact,shapeEqHOL]) valid
    let handlerEntry := ErrorHandler.entry source bodyPost input error
    have handled : evaluateHOLFiniteState caller program=evaluateHOLFiniteState handlerEntry handler := by rw [program_shape]; exact caught
    have handlerForward := evaluateHOLFiniteState_clock_le handlerEntry handler
    have callerContext := DecoderSetup.entered_context source input
    have callerCode : caller.code=source.code := by have h := congrArg PanSemStateFiniteExact.code callerContext; exact h
    have callerDomain : caller.memaddrs=source.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs callerContext; exact h
    have handlerCost := ErrorHandler.entry_cost input before source bodyPost error copied bounded (fields.2.2.2.trans callerCode) (fields.1.trans callerDomain)
    have actualSequence : evaluateHOLFiniteState caller DecoderSetup.decoder=evaluateHOLFiniteState handlerEntry handler := by
      rw [original_shape,← program_shape]
      have stopped : NoFallthrough handler := ErrorHandler.stopped
      rw [evaluateHOLFiniteState_seq_line780,handled]
      generalize h : evaluateHOLFiniteState handlerEntry handler=output at handlerForward ⊢
      obtain ⟨handlerResult,handlerPost⟩ := output
      cases handlerResult with
      | none => exact False.elim (stopped handlerEntry (by rw [h]))
      | some response => rfl
    have endpoint : target.clock=(evaluateHOLFiniteState handlerEntry handler).2.clock := (congrArg (fun output => output.2.clock) (actualSequence.symm.trans run)).symm
    change bodyPost.clock-(evaluateHOLFiniteState handlerEntry handler).2.clock≤51 at handlerCost
    change caller.clock-1-bodyPost.clock≤(input.length%2^64)/4+witnessLength input/2+522 at cost
    change (evaluateHOLFiniteState handlerEntry handler).2.clock≤bodyPost.clock at handlerForward
    exact Or.inl (by change caller.clock-target.clock≤_; rw [endpoint]; omega)
  · obtain ⟨same,data,image,records,hashes,requests,ffi,payloadLayout,layout⟩ := normal
    have actualBody : evaluateHOLFiniteState entry Header.body=(some (.returned (.val (.word (RequestPrefix.cursor input)))),bodyPost) := by rw [bodyRun,same]
    have validFinite : isValidValueHOLFinite caller .local (ofString "si") (.val (.word (RequestPrefix.cursor input)))=true := by
      simp [isValidValueHOLFinite,lookupKvarHOLFinite,callerSi,shapeOfHOLExact,shapeEqHOL]
    have valid : isValidValueHOLExact caller.toExact .local (ofString "si") (.val (.word (RequestPrefix.cursor input)))=true := by simpa only [isValidValueHOLFinite_eq] using validFinite
    have returned := evaluateHOLFiniteState_call_return_set_kvar caller .local (ofString "si") (some (ofString "SszErr",ofString "err_code",handler))
      (ofString "decode_stateless_input") arguments (values inputPointer (input.length%2^64)) Header.body callee .one (.val (.word (RequestPrefix.cursor input))) bodyPost args called (by omega) actualBody (by simp [shapeOfHOLExact,shapeEqHOL]) valid
    let current := setKvarHOLFinite .local (ofString "si") (.val (.word (RequestPrefix.cursor input))) {bodyPost with locals:=caller.locals}
    have forward : current.clock≤caller.clock := by change bodyPost.clock≤caller.clock; omega
    have otherGlobals (key : MlS) (different : key≠ofString "heap_ptr") : current.globals.lookup key=caller.globals.lookup key := by
      have preserved := ParserGlobals.decoder key entry.code environment.code different entry rfl
      rw [bodyRun] at preserved
      exact congrArg Prod.snd preserved
    have ready : DecoderReady input caller current := ⟨rfl,by simp [current,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
      WitnessDecoded.of_frame input bodyPost current rfl data,
      Payload.Image.of_memory bodyPost current input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) rfl image,
      VarList.Records.of_memory bodyPost current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) _ _ rfl records,RequestHashImage.of_memory input bodyPost current rfl hashes,RequestsDecoded.of_memory input bodyPost current rfl requests,ffi,otherGlobals,fields.2.2.2,fields.1,fields.2.2.1,fields.2.1,forward,by
        change caller.clock-1-bodyPost.clock≤(input.length%2^64)/4+witnessLength input/2+522 at cost
        change caller.clock-bodyPost.clock≤_; omega,payloadLayout,layout⟩
    rw [original_shape,StateSteps.next_sequence caller current _ _ returned forward] at run
    exact Or.inr ⟨current,ready,run⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.decoder_call_trace
