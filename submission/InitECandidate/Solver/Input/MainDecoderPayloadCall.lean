import InitECandidate.Solver.Input.MainDecoderRequestOffsets
import InitECandidate.Solver.Input.PayloadCallTrace

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure PayloadEntry (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  frame : ParserFrame source current (PersistentAlloc.rounded (RequestPrefix.cursor input) 96#64) 11
  bytes : Blob.HeapInput current input inputPointer
  pointer : current.locals.lookup (ofString "p") = some (.val (.word (inputPointer + 62#64)))
  length : current.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22 - 44))))

/-- Actual main-derived decoding through the original payload caller and
minimum-length guard. Passing exposes the real non-timeout callee body with
copied bytes, contained >=540-byte slice and aggregate11tick prefix frame. -/
theorem payload_call_trace (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (passes : ¬ Rejects input)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Header.body = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64 ∨ error = 81#64 ∨ error = 50#64) ∧
      result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 12) ∨
    (RequestLayout input ∧ 602 ≤ input.length % 2^64 ∧ 540 ≤ Guest.GasLimit.le32 input 22 - 44 ∧
      Guest.GasLimit.le32 input 22 - 44 ≤ input.length % 2^64 - 62 ∧
      ∃ (current innerPost : PanSemStateFiniteExact 64 Guest.HostMemory)
        (restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory → PanSemStateFiniteExact 64 Guest.HostMemory)
        (callee : HolFiniteMapExact MlS (ValueHOL 64)) (bodyResult : Option (PanSemResultExact 64)) (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory),
        PayloadCaller input source current ∧ evaluateHOLFiniteState current Request.continuation = (result,innerPost) ∧ post = restoreStack innerPost ∧
        (∀ target,emptyLocalsHOLFinite (restoreStack target) = emptyLocalsHOLFinite target) ∧
        evalListHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) Request.payloadArguments =
          some (Payload.values (inputPointer + 62#64) (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22 - 44))) ∧
        lookupCodeHOLFinite current.code.lookup (ofString "decode_payload") (Payload.values (inputPointer + 62#64) (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22 - 44))) = some (Payload.body,callee,.one) ∧
        1 ≤ current.clock ∧ PayloadEntry input source (callEntryStateHOLFinite current callee) ∧ bodyResult ≠ some .timeOut ∧
        evaluateHOLFiniteState (callEntryStateHOLFinite current callee) Payload.afterGuard = (bodyResult,bodyPost)) := by
  rcases request_offsets_trace input source post environment bounded passes result run notTimeout with fault | normal
  · obtain ⟨error,allowed,same,cost⟩ := fault
    refine Or.inl ⟨error,?_,same,by omega⟩
    rcases allowed with rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨layout,current,innerPost,restoreStack,caller,currentRun,restored,preserved⟩ := normal
    have hashesUpper : Guest.GasLimit.le32 input 22 ≤ input.length % 2^64 - 18 := by
      have first := layout.offsetsOrdered
      have second := layout.hashesUpper
      have third := layout.requestUpper
      omega
    obtain ⟨args,sliceUpper⟩ := Request.payload_arguments current input inputPointer caller.np caller.payloadOffset caller.hashesOffset layout.requestFixed layout.payloadLower hashesUpper layout.extent
    let length := BitVec.ofNat 64 (Guest.GasLimit.le32 input 22 - 44)
    have lengthNumber : length.toNat = Guest.GasLimit.le32 input 22 - 44 := by
      have small : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have payloadCode : current.code.lookup (ofString "decode_payload") = some (Payload.formals,Payload.body,.one) := by
      rw [caller.frame.code]
      exact Payload.original_code source.code environment.code
    have failCode : current.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one) := by
      rw [caller.frame.code]
      exact original_fail_code source.code environment.code
    have shape : current.eshapes.lookup (ofString "SszErr") = some .one := by rw [caller.frame.exceptions]; exact environment.shapes .SszErr
    have invocation := currentRun
    rw [Request.payload_call_shape] at invocation
    rcases Payload.call_trace current innerPost Request.payloadArguments Request.afterPayload (inputPointer + 62#64) length args payloadCode failCode shape result invocation notTimeout with short | valid
    · obtain ⟨_,same,cost⟩ := short
      have endClock : post.clock = innerPost.clock := by
        have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) (preserved innerPost)
        rw [restored]
        exact projected
      have afterClock := evaluateHOLFiniteState_clock_le current Request.continuation
      rw [currentRun] at afterClock
      change innerPost.clock ≤ current.clock at afterClock
      have before := caller.frame.clockLower
      have forward := caller.frame.forward
      exact Or.inl ⟨50#64,Or.inr (Or.inr (Or.inr (Or.inr rfl))),same,by rw [endClock]; omega⟩
    · obtain ⟨minimum,callee,bodyResult,bodyPost,called,p,n,funded,bodyNotTimeout,bodyRun⟩ := valid
      rw [lengthNumber] at minimum
      let entry := callEntryStateHOLFinite current callee
      have context : InitializerAllocations.context entry = InitializerAllocations.context current := rfl
      have frame := ParserFrame.advance source current entry _ _ 10 1 caller.frame context caller.frame.globals (Nat.sub_le _ _) (Nat.le_refl _)
      have entryBytes := Blob.HeapInput.of_fields current entry input inputPointer rfl rfl rfl caller.bytes
      have actualEntry : PayloadEntry input source entry := ⟨frame,entryBytes,p,n⟩
      exact Or.inr ⟨layout,by omega,minimum,sliceUpper,current,innerPost,restoreStack,callee,bodyResult,bodyPost,caller,currentRun,restored,preserved,args,called,funded,actualEntry,bodyNotTimeout,bodyRun⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.payload_call_trace
