import InitECandidate.Solver.Input.MainPayloadFields
import InitECandidate.Solver.Input.PayloadOffsetsTrace

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure OffsetLayout (input : Guest.InputBlob) : Prop where
  first : Payload.offsetWords input 0 = 540#64
  valid : ∀ position < 4,Offsets.ValidAt 540#64 (length input) (Payload.offsetWords input) position

structure OffsetReady (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  frame : ParserFrame source current (PersistentAlloc.rounded (cursor input) 136#64) 18
  bytes : Blob.HeapInput current input inputPointer
  pointer : current.locals.lookup (ofString "p") = some (.val (.word (inputPointer + 62#64)))
  length : current.locals.lookup (ofString "len") = some (.val (.word (PayloadPrefix.length input)))
  payload : current.locals.lookup (ofString "pl") = some (.val (.word (cursor input)))
  extra : current.locals.lookup (ofString "o_extra") = some (.val (.word (Payload.offsetWords input 0)))
  transactions : current.locals.lookup (ofString "o_txs") = some (.val (.word (Payload.offsetWords input 1)))
  withdrawals : current.locals.lookup (ofString "o_wd") = some (.val (.word (Payload.offsetWords input 2)))
  balances : current.locals.lookup (ofString "o_bal") = some (.val (.word (Payload.offsetWords input 3)))

private theorem offsets_context (current : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (clock : Nat) :
    InitializerAllocations.context {Payload.offsetsStored current input 2713715344#64 with clock := clock} = InitializerAllocations.context current := rfl

private theorem phase_clocks (source prepared next paid : Nat) (bound : paid ≤ 6)
    (first : prepared = source - 1) (second : next = prepared - paid) : next ≤ source ∧ source - 7 ≤ next := by omega

private theorem normal_frontier (input : Guest.InputBlob) (source entry prepared next : PanSemStateFiniteExact 64 Guest.HostMemory) (paid : Nat)
    (initialFrame : ParserFrame source prepared (PersistentAlloc.rounded (cursor input) 136#64) 12)
    (preparedClock : prepared.clock = entry.clock - 1) (bound : paid ≤ 6)
    (nextEq : next = {Payload.offsetsStored prepared input 2713715344#64 with clock := prepared.clock - paid})
    (nextBytes : Blob.HeapInput next input inputPointer)
    (pointerReady : prepared.locals.lookup (ofString "p") = some (.val (.word (inputPointer + 62#64))))
    (lengthReady : prepared.locals.lookup (ofString "len") = some (.val (.word (length input))))
    (payloadReady : prepared.locals.lookup (ofString "pl") = some (.val (.word (cursor input))))
    (fields : prepared.locals.lookup (ofString "o_extra") = some (.val (.word (Payload.offsetWords input 0))) ∧
      prepared.locals.lookup (ofString "o_txs") = some (.val (.word (Payload.offsetWords input 1))) ∧
      prepared.locals.lookup (ofString "o_wd") = some (.val (.word (Payload.offsetWords input 2))) ∧
      prepared.locals.lookup (ofString "o_bal") = some (.val (.word (Payload.offsetWords input 3)))) :
    OffsetReady input source next ∧ next.clock ≤ entry.clock ∧ entry.clock - 7 ≤ next.clock := by
  have context := (congrArg InitializerAllocations.context nextEq).trans (offsets_context prepared input (prepared.clock - paid))
  have globals : next.globals = prepared.globals := by
    have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) nextEq
    exact projected
  have nextClock : next.clock = prepared.clock - paid := by
    have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) nextEq
    exact projected
  have frame := ParserFrame.advance source prepared next _ _ 12 6 initialFrame context (globals.trans initialFrame.globals) (by rw [nextClock]; omega) (by rw [nextClock]; omega)
  have locals : next.locals = prepared.locals := by
    have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.locals) nextEq
    exact projected
  have lookup (key : String) : next.locals.lookup (ofString key) = prepared.locals.lookup (ofString key) := congrArg (fun map => map.lookup (ofString key)) locals
  have reached : OffsetReady input source next := ⟨frame,nextBytes,(lookup "p").trans pointerReady,
    (lookup "len").trans lengthReady,(lookup "pl").trans payloadReady,
    (lookup "o_extra").trans fields.1,(lookup "o_txs").trans fields.2.1,(lookup "o_wd").trans fields.2.2.1,(lookup "o_bal").trans fields.2.2.2⟩
  have bodyClocks := phase_clocks entry.clock prepared.clock next.clock paid bound preparedClock nextClock
  exact ⟨reached,bodyClocks.1,bodyClocks.2⟩

/-- The actual original payload allocation/header/offset prefix either
raises SszErr within7 body ticks (18 aggregate decoder-prefix ticks), or
reaches its real extra-data guard with every current byte/local and all four
validated offsets. No full budget or normal payload return is assumed. -/
theorem offsets_trace (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actual : DecoderCall.PayloadEntry input source entry)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (extent : 602 ≤ input.length % 2^64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState entry Payload.afterGuard = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧
      entry.clock - post.clock ≤ 7 ∧ source.clock - post.clock ≤ 18) ∨
    (OffsetLayout input ∧ ∃ (current innerPost : PanSemStateFiniteExact 64 Guest.HostMemory),OffsetReady input source current ∧ current.clock ≤ entry.clock ∧ entry.clock - 7 ≤ current.clock ∧
      evaluateHOLFiniteState current Payload.offsetContinuation = (result,innerPost) ∧
      post = Payload.restorePrefix entry input inputPointer (cursor input) (length input) innerPost ∧
      (∀ target,emptyLocalsHOLFinite (Payload.restorePrefix entry input inputPointer (cursor input) (length input) target) = emptyLocalsHOLFinite target)) := by
  obtain ⟨funded,innerPost,setup,bytes,remaining,restored⟩ := setup_trace input source entry post environment actual bounded extent result run notTimeout
  have initialFrame := ready_frame input source entry actual
  have offsets : (ready entry input).globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) := by
    rw [initialFrame.globals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "heap_ptr" == ofString "ssz_offs") = false from by decide] using environment.offsets
  have domain : (ready entry input).memaddrs = InitE.ordinaryDomain := initialFrame.domain.trans environment.domain
  have upper : inputPointer.toNat + input.length % 2^64 + 8 ≤ 33806089496 := by
    change 2713731432 + input.length % 2^64 + 8 ≤ 33806089496
    have bound : input.length % 2^64 ≤ 134217712 := bounded
    omega
  have offsetCode : (ready entry input).code.lookup (ofString "ssz_check_offsets") = some (Offsets.formals,Offsets.body,.one) := by rw [initialFrame.code]; exact DecoderCall.original_offsets_code source.code environment.code
  have failCode : (ready entry input).code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one) := by rw [initialFrame.code]; exact DecoderCall.original_fail_code source.code environment.code
  have shape : (ready entry input).eshapes.lookup (ofString "SszErr") = some .one := by rw [initialFrame.exceptions]; exact environment.shapes .SszErr
  have fields := ready_offsets entry input
  have pointerReady := ready_pointer entry input actual.pointer
  have lengthReady := ready_length entry input actual.length
  have payloadReady := ready_pl entry input
  have preparedClock := ready_clock entry input
  generalize preparedEq : ready entry input = prepared at *
  rcases Payload.offsets_trace prepared innerPost input inputPointer 2713715344#64 (length input) bytes offsets fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 domain
    (by decide) (by decide) upper (by decide) (by decide) lengthReady offsetCode failCode shape result remaining notTimeout with fault | normal
  · obtain ⟨error,allowed,same,cost⟩ := fault
    have endpoint : post.clock = innerPost.clock := by
      have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) (ProgramPrefix.restoration_frame setup innerPost)
      rw [restored]
      exact projected
    have after := evaluateHOLFiniteState_clock_le prepared Payload.offsetBody
    rw [remaining] at after
    change innerPost.clock ≤ prepared.clock at after
    have before := initialFrame.clockLower
    have forward := initialFrame.forward
    have clock := preparedClock
    exact Or.inl ⟨error,allowed,same,by rw [endpoint]; omega,by rw [endpoint]; omega⟩
  · obtain ⟨first,valid,next,paid,bound,enough,nextEq,nextBytes,nextRun⟩ := normal
    obtain ⟨reached,bodyForward,bodyLower⟩ := normal_frontier input source entry prepared next paid initialFrame preparedClock bound nextEq nextBytes pointerReady lengthReady payloadReady fields
    exact Or.inr ⟨⟨first,valid⟩,next,innerPost,reached,bodyForward,bodyLower,nextRun,restored,fun target => restore_frame entry target input⟩

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.offsets_trace
