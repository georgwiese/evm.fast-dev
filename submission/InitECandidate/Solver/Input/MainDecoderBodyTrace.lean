import InitECandidate.Solver.Input.MainPayloadBodyTrace
import InitECandidate.Solver.Input.MainHashFields
import InitECandidate.Solver.Input.MainRequestsWitnessTrace
import InitECandidate.Solver.Input.MainHashImageFrame

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The entire unchanged input decoder after the initial header checks,
from main's actual reached callee state to its observed result. All payload,
hash-count, request and witness parser failures are included; normal results
carry actual physical witness records through every restored caller scope. -/
theorem decoder_body_trace (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (bounded : input.length%2^64≤Guest.maxInputBytes) (passes : ¬Rejects input)
    (gas : Guest.GasLimit.declaredGasLimit input≤200000000)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Header.body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(input.length%2^64)/4+witnessLength input/2+522 ∧
      ((∃ error : BitVec 64,result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨
       (result=some (.returned (.val (.word (RequestPrefix.cursor input)))) ∧ WitnessDecoded input post ∧ Payload.Image post input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) ∧ VarList.Records post input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) ∧ RequestHashImage input post ∧ RequestsDecoded input post ∧ post.ffi=source.ffi)) := by
  rcases payload_call_trace input source post environment bounded passes result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    exact ⟨by omega,Or.inl ⟨error,same⟩⟩
  obtain ⟨layout,extent,minimum,sliceUpper,caller,callerPost,restoreStack,callee,bodyResult,bodyPost,callerData,callerRun,headerRestored,preserved,args,called,funded,entry,bodyNonTimeout,bodyRun⟩ := normal
  have lengthNumber : (PayloadPrefix.length input).toNat=Guest.GasLimit.le32 input 22-44 := by
    have small := Nat.mod_lt input.length (show 0<2^64 by decide)
    rw [PayloadPrefix.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have passing := Payload.passing_entry (callEntryStateHOLFinite caller callee) (PayloadPrefix.length input) entry.length (by rw [lengthNumber]; exact minimum)
  have inside : 62+(PayloadPrefix.length input).toNat≤input.length%2^64 := by rw [lengthNumber]; omega
  obtain ⟨bodyCost,bodyAggregate,outcome⟩ := PayloadPrefix.body_trace input source (callEntryStateHOLFinite caller callee) bodyPost environment entry bounded extent inside bodyResult bodyRun bodyNonTimeout
  have headerClock : post.clock=callerPost.clock := by
    rw [headerRestored]
    have h := congrArg PanSemStateFiniteExact.clock (preserved callerPost)
    exact h
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    have fullBody : evaluateHOLFiniteState (callEntryStateHOLFinite caller callee) Payload.body=(some (.exception (ofString "SszErr") (.val (.word error))),bodyPost) := by rw [passing,bodyRun,same]
    have observed := callerRun
    rw [Request.payload_call_shape,evaluateHOLFiniteState_decCall_fixClockRewrite] at observed
    simp only [args,called,if_neg (show caller.clock≠0 by omega)] at observed
    rw [fullBody] at observed
    have endpoint : callerPost.clock=bodyPost.clock := by have h := congrArg (fun output => output.2.clock) observed; exact h.symm
    exact ⟨by rw [headerClock,endpoint]; omega,Or.inl ⟨error,(congrArg Prod.fst observed).symm⟩⟩
  have returnedRun : evaluateHOLFiniteState (callEntryStateHOLFinite caller callee) Payload.afterGuard=(some (.returned (.val (.word (PayloadPrefix.cursor input)))),bodyPost) := by rw [bodyRun,normal]
  obtain ⟨payloadNext,payloadPost,returned,payloadCost,payloadRun,payloadRestored⟩ := PayloadPrefix.resume_return input source caller bodyPost callerPost callee environment entry layout bounded extent minimum sliceUpper gas args called funded _ returnedRun result callerRun
  obtain ⟨stored,storedData,siCell,storedClock,hashRun⟩ := PayloadPrefix.after_pointer input source caller payloadNext payloadPost environment callerData returned bounded result payloadRun
  rcases PayloadPrefix.hash_fields_trace input source caller stored payloadPost environment callerData storedData layout bounded siCell result hashRun notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    have forward := evaluateHOLFiniteState_clock_le stored Request.hashesCall
    rw [hashRun] at forward
    change payloadPost.clock≤stored.clock at forward
    have endpoint : post.clock=payloadPost.clock := by rw [headerClock,payloadRestored]; rfl
    exact ⟨by rw [endpoint]; omega,Or.inl ⟨error,same⟩⟩
  obtain ⟨requestCaller,requestPost,requestData,requestRun,hashRestored⟩ := normal
  obtain ⟨cost,outcome⟩ := requests_witness_trace_frame input source requestCaller requestPost environment requestData layout bounded result requestRun notTimeout
  have frame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite requestPost := by
    rw [headerRestored]
    calc
      emptyLocalsHOLFinite (restoreStack callerPost)=emptyLocalsHOLFinite callerPost := preserved _
      _=emptyLocalsHOLFinite requestPost := by rw [payloadRestored,hashRestored]; rfl
  have clock : post.clock=requestPost.clock := by have h := congrArg PanSemStateFiniteExact.clock frame; exact h
  refine ⟨by rw [clock]; exact cost,?_⟩
  rcases outcome with rejected | normal
  · exact Or.inl rejected
  · obtain ⟨same,data,earlier,image,records,hashes,requests,ffi⟩ := normal
    have memory : post.memory=requestPost.memory := by have h := congrArg PanSemStateFiniteExact.memory frame; exact h
    exact Or.inr ⟨same,WitnessDecoded.of_frame input requestPost post frame data,
      Payload.Image.of_memory requestPost post input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) memory image,
      VarList.Records.of_memory requestPost post input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) _ _ memory records,RequestHashImage.of_memory input requestPost post memory hashes,RequestsDecoded.of_memory input requestPost post memory requests,(by have h := congrArg PanSemStateFiniteExact.ffi frame; exact h.trans ffi)⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.decoder_body_trace
