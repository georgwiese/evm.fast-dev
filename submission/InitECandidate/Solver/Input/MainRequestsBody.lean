import InitECandidate.Solver.Input.MainRequestsCall
import InitECandidate.Solver.Input.Requests.BodyTrace

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure RequestDecoded (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64) : Prop where
  bytes : Blob.HeapInput post input inputPointer
  bodyCost : entry.clock - post.clock ≤ 348
  forward : post.clock ≤ entry.clock
  cost : source.clock - post.clock ≤ (input.length % 2^64) / 4 + 502
  control : BackingLayout.control post = BackingLayout.control (PersistentAlloc.post entry (PayloadPrefix.finalCursor input) 80#64)
  heap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word (PersistentAlloc.rounded (PayloadPrefix.finalCursor input) 80#64)))
  payload : ∀ offset < 136,post.memory (PayloadPrefix.cursor input + BitVec.ofNat 64 offset) = entry.memory (PayloadPrefix.cursor input + BitVec.ofNat 64 offset)
  layout : Requests.Layout (Requests.offsetWord input (requestStart input)) (BitVec.ofNat 64 (requestLength input))
  image : Requests.Image post (inputPointer + BitVec.ofNat 64 (requestStart input)) (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) counts
  earlier : ∀ query,inputPointer.toNat≤query.toNat → query.toNat<(PayloadPrefix.finalCursor input).toNat → post.memory query=entry.memory query

/-- All real request decoding at main's actual reached callee, including every
original offset/list rejection. No clock allowance, parser validity or future
return is assumed; normal heap/image/payload-field facts are derived. -/
theorem requests_body (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (actual : RequestsEntry input source entry)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (inside : requestStart input + requestLength input ≤ input.length % 2^64) (minimum : 20 ≤ requestLength input)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState entry Requests.afterGuard = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64 ∨ error = 30#64 ∨ error = 31#64) ∧
      result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ entry.clock - post.clock ≤ 348 ∧ source.clock - post.clock ≤ (input.length % 2^64) / 4 + 502) ∨
    (result = some (.returned (.val (.word (PayloadPrefix.finalCursor input)))) ∧ ∃ counts : Nat → BitVec 64,RequestDecoded input source entry post counts) := by
  have geometry := input_cursor_bounds input bounded
  have lower : 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input := geometry.1
  have upper : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
  have bytes : input.length % 2^64 ≤ 134217712 := bounded
  have cursor := PayloadPrefix.final_cursor_geometry input bounded actual.transactions
  have plCursor := (PayloadPrefix.cursor_number input bounded).1
  have installed : OriginalCode.Installed entry.code := actual.code.symm ▸ environment.code
  have shape : entry.eshapes.lookup (ofString "SszErr") = some .one := by rw [actual.exceptions]; exact environment.shapes .SszErr
  have arena : AllocatedBytes.Arena (PayloadPrefix.finalCursor input) 80 := ⟨by have h := cursor.2.2.1; omega,by have h := cursor.2.2.2; omega⟩
  have afterInput : inputPointer.toNat + input.length % 2^64 + 8 ≤ (PayloadPrefix.finalCursor input).toNat := by
    change 2713731432 + input.length % 2^64 + 8 ≤ _
    have h := cursor.2.2.1
    omega
  rcases Requests.after_guard_body entry post input inputPointer 2713715344#64 (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (requestStart input)
    actual.bytes (by omega) actual.pointer actual.length actual.offsets installed shape (actual.domain.trans environment.domain) (by decide) (by decide) (by decide) (by decide)
    (by change 2713731432 + input.length % 2^64 + 8 ≤ 33806089496; omega) arena cursor.2.1 actual.heap afterInput result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    have forward := evaluateHOLFiniteState_clock_le entry Requests.afterGuard
    rw [run] at forward
    change post.clock ≤ entry.clock at forward
    have before := actual.forward
    have prefixCost := actual.cost
    exact Or.inl ⟨error,allowed,same,cost,by omega⟩
  · obtain ⟨same,postBytes,cost,forward,control,outside,layout,counts,image⟩ := normal
    have before := actual.forward
    have prefixCost := actual.cost
    have heap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word (PersistentAlloc.rounded (PayloadPrefix.finalCursor input) 80#64))) := by
      have globals : post.globals = entry.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded (PayloadPrefix.finalCursor input) 80#64))) := by
        have projected := congrArg PanSemStateFiniteExact.globals control
        exact projected
      rw [globals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE]
    have payload (offset : Nat) (small : offset < 136) : post.memory (PayloadPrefix.cursor input + BitVec.ofNat 64 offset) = entry.memory (PayloadPrefix.cursor input + BitVec.ofNat 64 offset) := by
      have encoded : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      have number : (PayloadPrefix.cursor input + BitVec.ofNat 64 offset).toNat = DecoderSetup.cursor input + 384 + offset := by
        rw [BitVec.toNat_add_of_lt (by rw [encoded,plCursor]; omega),encoded,plCursor]
      apply outside
      · exact Or.inr (by change 2713715344 + 40 ≤ _; rw [number]; omega)
      · exact Or.inl (by rw [number]; have h := cursor.2.2.1; omega)
    have earlier (query : BitVec 64) (lower : inputPointer.toNat≤query.toNat) (before : query.toNat<(PayloadPrefix.finalCursor input).toNat) : post.memory query=entry.memory query := by
      apply outside
      · right
        change 2713731432≤query.toNat at lower
        change 2713715344+40≤query.toNat
        omega
      · exact Or.inl before
    exact Or.inr ⟨same,counts,⟨postBytes,cost,forward,by omega,control,heap,payload,layout,image,earlier⟩⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.requests_body
