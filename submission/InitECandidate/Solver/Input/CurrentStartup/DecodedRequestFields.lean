import InitECandidate.Solver.Input.CurrentStartup.DecodedPayloadPointer

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
variable {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
variable {source current post caller : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {pointer statelessRecord record gasWord requestRecord : BitVec 64}
variable {payloadLength : Nat} {value : ValueHOL 64} {counts : Nat → BitVec 64}

/-- All three earlier hash metadata fields survive the actual request call. -/
theorem RequestCallerReturn.Result.metadata
    (data : RequestCallerReturn.Result (decoderOrigin := decoderOrigin) input caller current post
      pointer statelessRecord record gasWord requestRecord payloadLength counts value) :
    current.memory (statelessRecord + 8#64) = .word (pointer + 18#64 + Request.requestWords input 1) ∧
    current.memory (statelessRecord + 16#64) = .word (BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32)) ∧
    current.memory (statelessRecord + 24#64) = .word (pointer + 18#64 + 8#64) := by
  obtain ⟨entry, bodyPost, start, size, decoded, currentEq⟩ := data.decoded
  have context := decoded.origin.context
  have kept (offset : Nat) (small : offset ≤ 24) :
      current.memory (statelessRecord + BitVec.ofNat 64 offset) = caller.memory (statelessRecord + BitVec.ofNat 64 offset) := by
    apply data.earlier_memory
    · rw [context.si_field_number input caller pointer statelessRecord record gasWord payloadLength offset (by omega)]
      omega
    · rw [context.si_field_number input caller pointer statelessRecord record gasWord payloadLength offset (by omega)]
      have := context.recordAfter
      have := data.requestAfter
      omega
  have fields := decoded.origin.metadata.2
  exact ⟨(kept 8 (by decide)).trans fields.1, (kept 16 (by decide)).trans fields.2.1, (kept 24 (by decide)).trans fields.2.2⟩

/-- The real request-pointer store at si+32 leaves the earlier metadata intact. -/
theorem WitnessEntry.Result.metadata
    (data : WitnessEntry.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value) :
    current.memory (statelessRecord + 8#64) = .word (pointer + 18#64 + Request.requestWords input 1) ∧
    current.memory (statelessRecord + 16#64) = .word (BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32)) ∧
    current.memory (statelessRecord + 24#64) = .word (pointer + 18#64 + 8#64) := by
  obtain ⟨caller, previous, previousPost, counts, decoded, sourceEq⟩ := data.origin
  have kept (offset : Nat) (small : offset ≤ 24) :
      current.memory (statelessRecord + BitVec.ofNat 64 offset) = previous.memory (statelessRecord + BitVec.ofNat 64 offset) := by
    rw [data.prepared]
    change source.memory (statelessRecord + BitVec.ofNat 64 offset) = _
    rw [sourceEq]
    simp [WitnessRadix.StoreWord.put,
      decoded.context.si_fields_ne input previous pointer statelessRecord record gasWord payloadLength offset 32 (by omega) (by decide) (by omega)]
  have fields := decoded.metadata
  exact ⟨(kept 8 (by decide)).trans fields.1, (kept 16 (by decide)).trans fields.2.1, (kept 24 (by decide)).trans fields.2.2⟩

/-- These are the concrete SI8/16/24/32 cells consumed by the original root
hasher, all at this same selected decoder post-state. -/
theorem WitnessHeadersReturn.Snapshot.request_fields
    (snapshot : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input current
      pointer statelessRecord record gasWord requestRecord payloadLength) :
    current.memory (statelessRecord + 8#64) = .word (pointer + 18#64 + Request.requestWords input 1) ∧
    current.memory (statelessRecord + 16#64) = .word (BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32)) ∧
    current.memory (statelessRecord + 24#64) = .word (pointer + 18#64 + 8#64) ∧
    current.memory (statelessRecord + 32#64) = .word requestRecord := by
  have requestCell := snapshot.prefix_frame.request_cell
  obtain ⟨origin, prepared, originalPost, value, decoded, memory⟩ := snapshot.prefix_frame
  have fields := decoded.metadata
  exact ⟨(memory _ (WitnessProtected.si_field decoded.context 8 (by decide))).trans fields.1,
    (memory _ (WitnessProtected.si_field decoded.context 16 (by decide))).trans fields.2.1,
    (memory _ (WitnessProtected.si_field decoded.context 24 (by decide))).trans fields.2.2, requestCell⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn.Result.metadata
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessEntry.Result.metadata
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.request_fields
