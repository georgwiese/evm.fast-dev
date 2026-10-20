import InitECandidate.Solver.Input.MainDecoderRequest
import InitECandidate.Solver.Input.RequestOffsetsTrace
import InitECandidate.Solver.Input.RequestOffsetsFields
import InitECandidate.Solver.Input.RequestOffsetValues
import InitECandidate.Solver.Input.ParserFrame

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure RequestLayout (input : Guest.InputBlob) : Prop where
  outerFixed : Guest.GasLimit.le32 input 2 = 16
  requestFixed : Guest.GasLimit.le32 input 18 = 44
  extent : 62 ≤ input.length % 2^64
  requestLower : 44 ≤ Guest.GasLimit.le32 input 6 - 16
  requestUpper : Guest.GasLimit.le32 input 6 - 16 ≤ input.length % 2^64 - 18
  payloadLower : 44 ≤ Guest.GasLimit.le32 input 22
  offsetsOrdered : Guest.GasLimit.le32 input 22 ≤ Guest.GasLimit.le32 input 58
  hashesUpper : Guest.GasLimit.le32 input 58 ≤ Guest.GasLimit.le32 input 6 - 16

structure PayloadCaller (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  frame : ParserFrame source current (PersistentAlloc.rounded (RequestPrefix.cursor input) 96#64) 10
  bytes : Blob.HeapInput current input inputPointer
  np : current.locals.lookup (ofString "np") = some (.val (.word (inputPointer + 18#64)))
  length : current.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16))))
  si : current.locals.lookup (ofString "si") = some (.val (.word (RequestPrefix.cursor input)))
  payloadOffset : current.locals.lookup (ofString "o_pl") = some (.val (.word (Request.requestWords input 0)))
  hashesOffset : current.locals.lookup (ofString "o_vh") = some (.val (.word (Request.requestWords input 1)))
  requestsOffset : current.locals.lookup (ofString "o_rq") = some (.val (.word (Request.requestWords input 2)))

/-- The actual original decoder either rejects in its outer/request parsing
within10 source ticks, or reaches the genuine payload caller with validated
ordered slices, all current bytes/locals/globals and its complete FFI state. -/
theorem request_offsets_trace (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (passes : ¬ Rejects input)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Header.body = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64 ∨ error = 81#64) ∧
      result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 10) ∨
    (RequestLayout input ∧ ∃ (current innerPost : PanSemStateFiniteExact 64 Guest.HostMemory)
      (restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory → PanSemStateFiniteExact 64 Guest.HostMemory),
      PayloadCaller input source current ∧ evaluateHOLFiniteState current Request.continuation = (result,innerPost) ∧ post = restoreStack innerPost ∧
      (∀ target,emptyLocalsHOLFinite (restoreStack target) = emptyLocalsHOLFinite target)) := by
  rcases request_trace input source post environment bounded passes result run notTimeout with fault | normal
  · obtain ⟨error,allowed,same,cost⟩ := fault
    exact Or.inl ⟨error,allowed,same,by omega⟩
  · obtain ⟨first,extent,minimum,totalUpper,ready,requestPost,restoreStack,metadata,forward,bytes,np,nlen,si,remaining,restored,preserved⟩ := normal
    let total := BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)
    have offsets : ready.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) := by
      rw [metadata.globals]
      simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "heap_ptr" == ofString "ssz_offs") = false from by decide] using environment.offsets
    have domain : ready.memaddrs = InitE.ordinaryDomain := metadata.domain.trans environment.domain
    have upper : inputPointer.toNat + input.length % 2^64 + 8 ≤ 33806089496 := by
      change 2713731432 + input.length % 2^64 + 8 ≤ 33806089496
      have small : input.length % 2^64 ≤ 134217712 := bounded
      omega
    have offsetCode : ready.code.lookup (ofString "ssz_check_offsets") = some (Offsets.formals,Offsets.body,.one) := by rw [metadata.code]; exact original_offsets_code source.code environment.code
    have failCode : ready.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one) := by rw [metadata.code]; exact original_fail_code source.code environment.code
    have shape : ready.eshapes.lookup (ofString "SszErr") = some .one := by rw [metadata.exceptions]; exact environment.shapes .SszErr
    rcases Request.offsets_trace ready requestPost input inputPointer 2713715344#64 total bytes extent np nlen offsets domain (by decide) (by decide) upper (by decide) (by decide)
      offsetCode failCode shape result remaining notTimeout with offsetFault | offsetNormal
    · obtain ⟨error,allowed,same,cost⟩ := offsetFault
      have afterClock := evaluateHOLFiniteState_clock_le ready Request.requestBody
      rw [remaining] at afterClock
      change requestPost.clock ≤ ready.clock at afterClock
      have endpoint : post.clock = requestPost.clock := by
        have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) (preserved requestPost)
        rw [restored]
        exact projected
      have before := metadata.clockLower
      refine Or.inl ⟨error,?_,same,?_⟩
      · rcases allowed with rfl | rfl | rfl <;> simp
      · rw [endpoint]
        omega
    · obtain ⟨firstRequest,valid,next,innerPost,paid,bound,enough,nextEq,nextBytes,nextRun,requestRestored⟩ := offsetNormal
      obtain ⟨requestFixed,payloadLower,ordered,hashesUpper⟩ := Request.request_values input total firstRequest valid
      have totalNumber : total.toNat = Guest.GasLimit.le32 input 6 - 16 := by
        have small : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      rw [totalNumber] at hashesUpper
      have initialFrame := ParserFrame.of_request source ready (RequestPrefix.cursor input) metadata forward
      have context : InitializerAllocations.context next = InitializerAllocations.context ready :=
        (congrArg InitializerAllocations.context nextEq).trans (Request.offsets_context ready input 2713715344#64 (ready.clock - paid))
      have nextGlobals : next.globals = ready.globals := by
        have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) nextEq
        exact projected
      have nextClock : next.clock = ready.clock - paid := by
        have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) nextEq
        exact projected
      have frame := ParserFrame.advance source ready next _ _ 5 5 initialFrame context (nextGlobals.trans metadata.globals)
        (by rw [nextClock]; omega) (by rw [nextClock]; omega)
      have other (key : String) (rq : ofString "o_rq" ≠ ofString key) (vh : ofString "o_vh" ≠ ofString key) (pl : ofString "o_pl" ≠ ofString key) :
          next.locals.lookup (ofString key) = ready.locals.lookup (ofString key) :=
        (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.locals.lookup (ofString key)) nextEq).trans
          (Request.offsets_other ready input 2713715344#64 key rq vh pl)
      have bindings := Request.offsets_bindings ready input 2713715344#64
      have pl := (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.locals.lookup (ofString "o_pl")) nextEq).trans bindings.1
      have vh := (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.locals.lookup (ofString "o_vh")) nextEq).trans bindings.2.1
      have rq := (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.locals.lookup (ofString "o_rq")) nextEq).trans bindings.2.2
      have caller : PayloadCaller input source next := ⟨frame,nextBytes,(other "np" (by decide) (by decide) (by decide)).trans np,
        (other "nlen" (by decide) (by decide) (by decide)).trans nlen,(other "si" (by decide) (by decide) (by decide)).trans si,pl,vh,rq⟩
      let finalRestore := fun target => restoreStack (Request.restoreOffsets ready input target)
      have finalEndpoint : post = finalRestore innerPost := by rw [restored,requestRestored]
      have finalFrame (target : PanSemStateFiniteExact 64 Guest.HostMemory) : emptyLocalsHOLFinite (finalRestore target) = emptyLocalsHOLFinite target :=
        (preserved (Request.restoreOffsets ready input target)).trans (Request.restore_offsets_frame ready target input)
      exact Or.inr ⟨⟨first,requestFixed,extent,minimum,totalUpper,payloadLower,ordered,hashesUpper⟩,next,innerPost,finalRestore,caller,nextRun,finalEndpoint,finalFrame⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.request_offsets_trace
