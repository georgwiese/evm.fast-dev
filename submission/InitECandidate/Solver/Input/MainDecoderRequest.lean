import InitECandidate.Solver.Input.MainRequestLength

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Actual original decoder through its outer container and request setup.
All offset/length rejections are retained. Passing derives the real request
slice and reaches the unchanged body with its actual bytes and full frame. -/
theorem request_trace (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (passes : ¬ Rejects input)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Header.body = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64 ∨ error = 81#64) ∧
      result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 6) ∨
    (Guest.GasLimit.le32 input 2 = 16 ∧ 62 ≤ input.length % 2^64 ∧
      44 ≤ Guest.GasLimit.le32 input 6 - 16 ∧ Guest.GasLimit.le32 input 6 - 16 ≤ input.length % 2^64 - 18 ∧
      ∃ (ready innerPost : PanSemStateFiniteExact 64 Guest.HostMemory) (restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory → PanSemStateFiniteExact 64 Guest.HostMemory),Request.ReadyFrame source ready (RequestPrefix.cursor input) ∧ ready.clock ≤ source.clock ∧
        Blob.HeapInput ready input inputPointer ∧
        ready.locals.lookup (ofString "np") = some (.val (.word (inputPointer + 18#64))) ∧
        ready.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)))) ∧
        evaluateHOLFiniteState ready Request.requestBody = (result,innerPost) ∧ post = restoreStack innerPost ∧
        (∀ target,emptyLocalsHOLFinite (restoreStack target) = emptyLocalsHOLFinite target)) := by
  have validEntry : 18 ≤ input.length % 2^64 ∧ Guest.GasLimit.byte input 0 = 21 ∧ Guest.GasLimit.byte input 1 = 1 := by
    simpa only [Rejects,not_or,not_lt,not_not] using passes
  rcases outer_trace input source post environment bounded passes result run notTimeout with fault | normal
  · obtain ⟨error,allowed,same,cost⟩ := fault
    exact Or.inl ⟨error,by rcases allowed with rfl | rfl | rfl <;> simp,same,by omega⟩
  · obtain ⟨first,witnessLower,witnessUpper,next,paid,bound,enough,nextEq,bytes,remaining⟩ := normal
    have asCurrent : next = RequestPrefix.current source input (source.clock - paid) := nextEq
    have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) asCurrent
    have domain := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) asCurrent
    have endian := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) asCurrent
    have currentBytes := Blob.HeapInput.of_fields next (RequestPrefix.current source input (source.clock - paid)) input inputPointer memory domain endian bytes
    have currentRun : evaluateHOLFiniteState (RequestPrefix.current source input (source.clock - paid)) Header.continuation = (result,post) :=
      (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => evaluateHOLFiniteState state Header.continuation) asCurrent.symm).trans remaining
    obtain ⟨funded,restoreStack,innerPost,setup,readyBytes,guardRun,restored⟩ := RequestPrefix.setup_trace input source post (source.clock - paid) environment bounded validEntry.1 first witnessLower currentBytes result currentRun notTimeout
    have preserved := ProgramPrefix.restoration_frame setup innerPost
    have postClock : post.clock = innerPost.clock := by
      have clock := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) preserved
      rw [restored]
      exact clock
    rcases RequestPrefix.length_trace input source innerPost (source.clock - paid) environment result guardRun notTimeout with short | valid
    · obtain ⟨_,_,same,endpoint⟩ := short
      have innerClock : innerPost.clock = source.clock - paid - 1 - 1 := by
        rw [endpoint]
        change (RequestPrefix.ready source input (source.clock - paid)).clock - 1 = _
        rw [RequestPrefix.ready_clock]
      exact Or.inl ⟨81#64,Or.inr (Or.inr (Or.inr rfl)),same,by rw [postClock,innerClock]; omega⟩
    · obtain ⟨minimum,requestRun⟩ := valid
      have metadata := RequestPrefix.ready_frame source input paid bound
      have bindings := RequestPrefix.ready_bindings source input (source.clock - paid)
      have clock : (RequestPrefix.ready source input (source.clock - paid)).clock ≤ source.clock := by rw [RequestPrefix.ready_clock]; omega
      exact Or.inr ⟨first,by omega,minimum,by omega,RequestPrefix.ready source input (source.clock - paid),innerPost,restoreStack,metadata,clock,readyBytes,
        bindings.1,bindings.2,requestRun,restored,ProgramPrefix.restoration_frame setup⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.request_trace
