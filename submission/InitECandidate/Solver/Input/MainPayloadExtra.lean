import InitECandidate.Solver.Input.MainPayloadOffsets
import InitECandidate.Solver.Input.PayloadExtraTrace

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual payload prefix includes every offset and extra-data rejection.
Passing proves <=32 extra bytes and reaches the literal original body with
its current state, all copied bytes and exact lexical-restoration evidence. -/
theorem extra_trace (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actual : DecoderCall.PayloadEntry input source entry)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (extent : 602 ≤ input.length % 2^64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState entry Payload.afterGuard = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64 ∨ error = 51#64) ∧
      result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ entry.clock - post.clock ≤ 8 ∧ source.clock - post.clock ≤ 19) ∨
    (OffsetLayout input ∧ Guest.GasLimit.le32 input 566 - 540 ≤ 32 ∧
      ∃ (current innerPost : PanSemStateFiniteExact 64 Guest.HostMemory),OffsetReady input source current ∧
        current.clock ≤ entry.clock ∧ entry.clock - 7 ≤ current.clock ∧
        evaluateHOLFiniteState current Payload.afterExtra = (result,innerPost) ∧
        post = Payload.restorePrefix entry input inputPointer (cursor input) (length input) innerPost ∧
        (∀ target,emptyLocalsHOLFinite (Payload.restorePrefix entry input inputPointer (cursor input) (length input) target) = emptyLocalsHOLFinite target)) := by
  rcases offsets_trace input source entry post environment actual bounded extent result run notTimeout with fault | normal
  · obtain ⟨error,allowed,same,bodyCost,prefixCost⟩ := fault
    refine Or.inl ⟨error,?_,same,by omega,by omega⟩
    rcases allowed with rfl | rfl | rfl <;> simp
  · obtain ⟨layout,current,innerPost,reached,bodyForward,bodyLower,remaining,restored,preserved⟩ := normal
    have extraLocal : current.locals.lookup (ofString "o_extra") = some (.val (.word 540#64)) := by simpa only [layout.first] using reached.extra
    have failCode : current.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one) := by
      rw [reached.frame.code]
      exact DecoderCall.original_fail_code source.code environment.code
    have shape : current.eshapes.lookup (ofString "SszErr") = some .one := by rw [reached.frame.exceptions]; exact environment.shapes .SszErr
    rcases Payload.extra_trace current innerPost input extraLocal reached.transactions (layout.valid 1 (by decide)).1 failCode shape result remaining notTimeout with invalid | valid
    · obtain ⟨_,_,same,endpoint⟩ := invalid
      have postClock : post.clock = current.clock - 1 := by
        have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) (preserved innerPost)
        rw [restored]
        change (Payload.restorePrefix entry input inputPointer (cursor input) (length input) innerPost).clock = _
        rw [show (Payload.restorePrefix entry input inputPointer (cursor input) (length input) innerPost).clock = innerPost.clock from projected,endpoint]
        rfl
      have before := reached.frame.clockLower
      have forward := reached.frame.forward
      exact Or.inl ⟨51#64,Or.inr (Or.inr (Or.inr rfl)),same,by rw [postClock]; omega,by rw [postClock]; omega⟩
    · obtain ⟨small,tailRun⟩ := valid
      change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)).toNat - 540 ≤ 32 at small
      rw [Request.le32_number input 566 (by decide)] at small
      exact Or.inr ⟨layout,small,current,innerPost,reached,bodyForward,bodyLower,tailRun,restored,preserved⟩

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.extra_trace
