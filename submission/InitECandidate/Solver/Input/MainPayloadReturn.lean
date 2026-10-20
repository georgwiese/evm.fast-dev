import InitECandidate.Solver.Input.MainPayloadNormal
import InitECandidate.Solver.Input.EvaluationFields
import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.Input.ParserGlobals

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure Returned (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  locals : current.locals = caller.locals.update (ofString "pl",.val (.word (cursor input)))
  bytes : Blob.HeapInput current input inputPointer
  gasCell : current.memory (cursor input + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474))
  gasBound : (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)).toNat ≤ 200000000
  countCell : current.memory (cursor input + 56#64) = .word (BitVec.ofNat 64 (Payload.withdrawalCount input))
  code : current.code = caller.code
  domain : current.memaddrs = caller.memaddrs
  endian : current.be = caller.be
  exceptions : current.eshapes = caller.eshapes
  heap : current.globals.lookup (ofString "heap_ptr") = some (.val (.word (finalCursor input)))
  transactions : Payload.transactionCount input ≤ (input.length % 2^64) / 4
  globals : ∀ key,key ≠ ofString "heap_ptr" → current.globals.lookup key = caller.globals.lookup key
  forward : current.clock ≤ caller.clock
  cost : caller.clock - current.clock ≤ (input.length % 2^64) / 4 + 76

/-- Resume the real original payload caller after its observed normal callee
return, retaining an arbitrary actual enclosing result. The later request/
witness continuation is not assumed successful. All payload fields and the
actual caller binding are derived from the same complete payload execution. -/
theorem resume_return (input : Guest.InputBlob) (source caller bodyPost post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (environment : DecoderCall.Environment input source)
    (entry : DecoderCall.PayloadEntry input source (callEntryStateHOLFinite caller callee))
    (layout : DecoderCall.RequestLayout input) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (extent : 602 ≤ input.length % 2^64) (minimum : 540 ≤ Guest.GasLimit.le32 input 22 - 44)
    (sliceUpper : Guest.GasLimit.le32 input 22 - 44 ≤ input.length % 2^64 - 62)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (args : evalListHOLFinite caller (h := fun address => Classical.propDecidable (caller.memaddrs address)) Request.payloadArguments =
      some (Payload.values (inputPointer + 62#64) (length input)))
    (called : lookupCodeHOLFinite caller.code.lookup (ofString "decode_payload") (Payload.values (inputPointer + 62#64) (length input)) = some (Payload.body,callee,.one))
    (funded : 1 ≤ caller.clock) (returned : ValueHOL 64)
    (bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite caller callee) Payload.afterGuard = (some (.returned returned),bodyPost))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState caller Request.continuation = (result,post)) :
    ∃ current final,Returned input caller current ∧ source.clock - current.clock ≤ (input.length % 2^64) / 4 + 86 ∧
      evaluateHOLFiniteState current Request.afterPayload = (result,final) ∧ post = QueryBranch.restore caller "pl" final := by
  obtain ⟨valueEq,gasCell,gasBound,countCell,bytes,cost,_,aggregate,forward,heapCursor,countBound⟩ := normal_payload input source (callEntryStateHOLFinite caller callee) bodyPost environment entry layout bounded extent minimum sliceUpper gas returned bodyRun
  have lengthNumber : (length input).toNat = Guest.GasLimit.le32 input 22 - 44 := by
    have small : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
    rw [length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have fullBody := (Payload.passing_entry (callEntryStateHOLFinite caller callee) (length input) entry.length (by rw [lengthNumber]; exact minimum)).trans bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one) = true := by
    rw [valueEq]
    simp [shapeOfHOLExact,shapeEqHOL]
  have actual := CallNormal.return_execute caller bodyPost "pl" .one (ofString "decode_payload") Request.payloadArguments (Payload.values (inputPointer + 62#64) (length input))
    Payload.body Request.afterPayload callee .one returned args called funded fullBody shapePass
  rw [Request.payload_call_shape] at run
  have continued := actual.symm.trans run
  let current := CallNormal.continuationEntry caller bodyPost "pl" returned
  let final := (evaluateHOLFiniteState current Request.afterPayload).2
  have observed := congrArg Prod.fst continued
  have endpoint : post = QueryBranch.restore caller "pl" final := (congrArg Prod.snd continued).symm
  have fields := evaluation_fields (callEntryStateHOLFinite caller callee) bodyPost Payload.afterGuard (some (.returned returned)) bodyRun
  have locals : current.locals = caller.locals.update (ofString "pl",.val (.word (cursor input))) := by
    change caller.locals.update (ofString "pl",returned) = _
    rw [valueEq]
  have currentBytes := Blob.HeapInput.of_fields bodyPost current input inputPointer rfl rfl rfl bytes
  have currentForward : current.clock ≤ caller.clock := by change bodyPost.clock ≤ caller.clock; change bodyPost.clock ≤ caller.clock - 1 at forward; omega
  have currentCost : caller.clock - current.clock ≤ (input.length % 2^64) / 4 + 76 := by
    change caller.clock - 1 - bodyPost.clock ≤ (input.length % 2^64) / 4 + 75 at cost
    change bodyPost.clock ≤ caller.clock - 1 at forward
    change caller.clock - bodyPost.clock ≤ _
    omega
  have installed : OriginalCode.Installed (callEntryStateHOLFinite caller callee).code := entry.frame.code.symm ▸ environment.code
  have globals (key : MlS) (other : key ≠ ofString "heap_ptr") : current.globals.lookup key = caller.globals.lookup key := by
    have frame := ParserGlobals.payload key (callEntryStateHOLFinite caller callee).code installed other (callEntryStateHOLFinite caller callee) rfl
    rw [fullBody] at frame
    exact congrArg Prod.snd frame
  have reached : Returned input caller current := ⟨locals,currentBytes,gasCell,gasBound,countCell,fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,heapCursor,countBound,globals,currentForward,currentCost⟩
  exact ⟨current,final,reached,aggregate,Prod.ext observed rfl,endpoint⟩

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.resume_return
