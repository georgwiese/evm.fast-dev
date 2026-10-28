import InitECandidate.Solver.Input.CurrentStartup.WitnessSnapshot
import InitECandidate.Solver.Input.CurrentStartup.CallerSiBase

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
variable {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
variable {source current post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {pointer statelessRecord record gasWord requestRecord array nodes codes headers : BitVec 64}
variable {payloadLength start length nodeStart nodeLength codeStart codeLength : Nat} {value : ValueHOL 64}

/-- Earlier records are below the new witness arrays. Only the six concrete
witness-pointer/count output cells may change within this interval. -/
structure WitnessProtected (statelessRecord record requestRecord query : BitVec 64) : Prop where
  lower : statelessRecord.toNat ≤ query.toNat
  upper : query.toNat < max (record.toNat + 136) (requestRecord.toNat + 80)
  away : ∀ offset ∈ ([40, 48, 56, 64, 72, 80] : List Nat), query ≠ statelessRecord + BitVec.ofNat 64 offset

theorem WitnessProtected.si_field
    (context : PayloadCallerReturn.Context input source pointer statelessRecord record gasWord payloadLength)
    (offset : Nat) (small : offset ≤ 32) :
    WitnessProtected statelessRecord record requestRecord (statelessRecord + BitVec.ofNat 64 offset) := by
  have number := context.si_field_number input source pointer statelessRecord record gasWord payloadLength offset (by omega)
  refine ⟨by rw [number]; omega, ?_, ?_⟩
  · rw [number]
    have := context.recordAfter
    omega
  · intro other member
    have bound : 40 ≤ other ∧ other ≤ 80 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    exact context.si_fields_ne input source pointer statelessRecord record gasWord payloadLength offset other (by omega) (by omega) (by omega)

/-- Earlier cells at this exact later state come from the same actual witness
entry. This includes payload and request records, rather than just si+0. -/
def WitnessPrefixFrame (decoderOrigin : DecoderOrigin) (input : Guest.InputBlob)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) : Prop :=
  ∃ source current post value,
    WitnessEntry.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value ∧
    ∀ query, WitnessProtected statelessRecord record requestRecord query → target.memory query = current.memory query

theorem WitnessPrefixFrame.of_memory
    (data : WitnessPrefixFrame decoderOrigin input source pointer statelessRecord record gasWord requestRecord payloadLength)
    (memory : ∀ query, WitnessProtected statelessRecord record requestRecord query → current.memory query = source.memory query) :
    WitnessPrefixFrame decoderOrigin input current pointer statelessRecord record gasWord requestRecord payloadLength := by
  obtain ⟨origin, prepared, originalPost, value, entry, frame⟩ := data
  exact ⟨origin, prepared, originalPost, value, entry, fun query region => (memory query region).trans (frame query region)⟩

theorem WitnessValidated.Result.prefix_frame
    (data : WitnessValidated.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value) :
    WitnessPrefixFrame decoderOrigin input current pointer statelessRecord record gasWord requestRecord payloadLength := by
  obtain ⟨caller, originalPost, decoded, frame, clock, memory⟩ := data.endpoint
  refine ⟨caller, source, originalPost, value, decoded, ?_⟩
  intro query region
  apply memory
  apply Or.inr
  have := data.context.pointerLower
  have := data.context.statelessLower
  have := region.lower
  omega

theorem WitnessLoaded.Result.prefix_frame
    (data : WitnessLoaded.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value) :
    WitnessPrefixFrame decoderOrigin input current pointer statelessRecord record gasWord requestRecord payloadLength := by
  obtain ⟨origin, originalPost, decoded, frame, clock⟩ := data.endpoint
  exact decoded.prefix_frame.of_memory (by intro query region; rw [data.prepared]; rfl)

theorem WitnessNodesReturn.Result.prefix_frame
    (data : WitnessNodesReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord array payloadLength start length value) :
    WitnessPrefixFrame decoderOrigin input current pointer statelessRecord record gasWord requestRecord payloadLength := by
  obtain ⟨origin, originalPost, decoded, endpoint⟩ := data.origin
  apply decoded.prefix_frame.of_memory
  intro query region
  apply data.memory
  · have := region.upper
    have := data.arrayAfter
    omega
  · exact region.away 40 (by decide)
  · exact region.away 48 (by decide)

theorem WitnessCodesReturn.Result.prefix_frame
    (data : WitnessCodesReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord nodes codes payloadLength nodeStart nodeLength start length value) :
    WitnessPrefixFrame decoderOrigin input current pointer statelessRecord record gasWord requestRecord payloadLength := by
  obtain ⟨origin, originalPost, decoded, endpoint⟩ := data.origin
  apply decoded.prefix_frame.of_memory
  intro query region
  apply data.memory
  · have := region.upper
    have := data.arrayAfter
    omega
  · exact region.away 56 (by decide)
  · exact region.away 64 (by decide)

theorem WitnessHeadersReturn.Result.prefix_frame
    (data : WitnessHeadersReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord nodes codes headers payloadLength nodeStart nodeLength codeStart codeLength start length) :
    WitnessPrefixFrame decoderOrigin input post pointer statelessRecord record gasWord requestRecord payloadLength := by
  obtain ⟨origin, decoded⟩ := data.origin
  apply decoded.prefix_frame.of_memory
  intro query region
  apply data.memory
  · have := region.upper
    have := data.arrayAfter
    omega
  · exact region.away 72 (by decide)
  · exact region.away 80 (by decide)

theorem WitnessHeadersReturn.Snapshot.prefix_frame
    (data : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input post
      pointer statelessRecord record gasWord requestRecord payloadLength) :
    WitnessPrefixFrame decoderOrigin input post pointer statelessRecord record gasWord requestRecord payloadLength := by
  obtain ⟨headerSource, ready, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    start, length, decoded, frame, clock⟩ := data
  apply decoded.prefix_frame.of_memory
  have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) frame
  change post.memory = headerPost.memory at memory
  intro query region
  rw [memory]

/-- The actual request-pointer output cell survives every witness stage. -/
theorem WitnessPrefixFrame.request_cell
    (data : WitnessPrefixFrame decoderOrigin input current pointer statelessRecord record gasWord requestRecord payloadLength) :
    current.memory (statelessRecord + 32#64) = .word requestRecord := by
  obtain ⟨origin, prepared, originalPost, value, decoded, memory⟩ := data
  exact (memory (statelessRecord + 32#64) (WitnessProtected.si_field decoded.context 32 (by decide))).trans decoded.requestCell

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessPrefixFrame.of_memory
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessValidated.Result.prefix_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessLoaded.Result.prefix_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessNodesReturn.Result.prefix_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessCodesReturn.Result.prefix_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Result.prefix_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.prefix_frame

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessProtected.si_field
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessPrefixFrame.request_cell
