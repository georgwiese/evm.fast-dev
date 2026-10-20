import InitECandidate.Solver.Input.MainRequestsCall
import InitECandidate.Solver.Input.Requests.OffsetsTrace

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Instantiate the original request offset loop/validator at its actual
reached callee. Failure costs at most12body ticks; normal progression reaches
the real80-byte allocator within encodedLength/4+166 aggregate source ticks. -/
theorem requests_offsets_trace (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (actual : RequestsEntry input source entry)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (inside : requestStart input + requestLength input ≤ input.length % 2^64)
    (minimum : 20 ≤ requestLength input)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState entry Requests.afterGuard = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧
      entry.clock - post.clock ≤ 12 ∧ source.clock - post.clock ≤ (input.length % 2^64) / 4 + 166) ∨
    (Requests.offsetWord input (requestStart input) 0 = 20#64 ∧
      (∀ position < 5,Offsets.ValidAt 20#64 (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) position) ∧
      ∃ next innerPost,next.clock ≤ entry.clock ∧ source.clock - next.clock ≤ (input.length % 2^64) / 4 + 166 ∧
        BackingLayout.control next = BackingLayout.control entry ∧ Blob.HeapInput next input inputPointer ∧
        next.globals.lookup (ofString "heap_ptr") = some (.val (.word (PayloadPrefix.finalCursor input))) ∧
        next.locals.lookup (ofString "p") = some (.val (.word (inputPointer + BitVec.ofNat 64 (requestStart input)))) ∧
        next.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (requestLength input)))) ∧
        (∀ position < 5,next.memory (WitnessRadix.byteAddress 2713715344#64 (8*position)) = .word (Requests.offsetWord input (requestStart input) position)) ∧
        evaluateHOLFiniteState next Requests.afterOffsets = (result,innerPost) ∧ post = QueryBranch.restore entry "i" innerPost) := by
  have installed : OriginalCode.Installed entry.code := actual.code.symm ▸ environment.code
  have upper : inputPointer.toNat + input.length % 2^64 + 8 ≤ 33806089496 := by
    change 2713731432 + input.length % 2^64 + 8 ≤ _
    have small : input.length % 2^64 ≤ 134217712 := bounded
    omega
  have shape : entry.eshapes.lookup (ofString "SszErr") = some .one := by rw [actual.exceptions]; exact environment.shapes .SszErr
  rcases Requests.offsets_trace entry post input inputPointer 2713715344#64 (BitVec.ofNat 64 (requestLength input)) (requestStart input)
    actual.bytes (by omega) actual.pointer actual.length actual.offsets (actual.domain.trans environment.domain) (by decide) (by decide) (by decide) (by decide) upper
    (original_offsets_code entry.code installed) (original_fail_code entry.code installed) shape result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    have forward := evaluateHOLFiniteState_clock_le entry Requests.afterGuard
    rw [run] at forward
    change post.clock ≤ entry.clock at forward
    have before := actual.forward
    have prefixCost := actual.cost
    exact Or.inl ⟨error,allowed,same,cost,by omega⟩
  · obtain ⟨first,valid,next,innerPost,forward,cost,control,bytes,other,cells,remaining,restored,memoryFrame⟩ := normal
    have globals : next.globals = entry.globals := by have projected := congrArg PanSemStateFiniteExact.globals control; exact projected
    have heap : next.globals.lookup (ofString "heap_ptr") = some (.val (.word (PayloadPrefix.finalCursor input))) := by rw [globals]; exact actual.heap
    have before := actual.forward
    have prefixCost := actual.cost
    exact Or.inr ⟨first,valid,next,innerPost,forward,by omega,control,bytes,heap,
      (other (ofString "p") (by decide)).trans actual.pointer,(other (ofString "len") (by decide)).trans actual.length,cells,remaining,restored⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.requests_offsets_trace
