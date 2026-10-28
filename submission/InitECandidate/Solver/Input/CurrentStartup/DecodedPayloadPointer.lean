import InitECandidate.Solver.Input.CurrentStartup.WitnessSnapshot
import InitECandidate.Solver.Input.CurrentStartup.RequestMetadataCells
import InitECandidate.Solver.Input.CurrentStartup.WitnessPrefixFrame

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
variable {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
variable {source current post caller entry : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {pointer statelessRecord record gasWord count requestRecord array nodes codes headers : BitVec 64}
variable {length payloadLength start size nodeStart nodeLength codeStart codeLength : Nat}
variable {value : ValueHOL 64} {counts : Nat → BitVec 64}

/-- The actual request call preserves every earlier high-memory cell below
its freshly allocated record; this also retains complete payload records. -/
theorem RequestCallerReturn.Result.earlier_memory
    (data : RequestCallerReturn.Result (decoderOrigin := decoderOrigin) input caller current post
      pointer statelessRecord record gasWord requestRecord payloadLength counts value)
    (query : BitVec 64) (afterSi : statelessRecord.toNat ≤ query.toNat) (beforeRequest : query.toNat < requestRecord.toNat) :
    current.memory query = caller.memory query := by
  obtain ⟨entry, bodyPost, start, size, decoded, currentEq⟩ := data.decoded
  have context := decoded.origin.context
  have outside : 2701132528 + 40 ≤ query.toNat := by
    have := context.statelessLower
    have := context.pointerLower
    omega
  have memory := decoded.memory query beforeRequest (Or.inr outside)
  obtain ⟨callee, parentPost, parentValue, entryEq, rest⟩ := decoded.origin.invocation
  have entryCell : entry.memory query = caller.memory query := by rw [entryEq]; rfl
  rw [currentEq]
  exact memory.trans entryCell

/-- The request decoder's workspace and fresh record are disjoint from si. -/
theorem RequestCallerReturn.Result.payload_cell
    (data : RequestCallerReturn.Result (decoderOrigin := decoderOrigin) input caller current post
      pointer statelessRecord record gasWord requestRecord payloadLength counts value) :
    current.memory statelessRecord = .word record := by
  obtain ⟨entry, bodyPost, start, size, decoded, currentEq⟩ := data.decoded
  have context := decoded.origin.context
  have before : statelessRecord.toNat < requestRecord.toNat := by
    have := context.recordAfter
    have := decoded.requestAfter
    omega
  exact (data.earlier_memory statelessRecord (Nat.le_refl _) before).trans decoded.origin.payload_cell

/-- The request-pointer store and witness declarations retain si+0. -/
theorem WitnessEntry.Result.payload_cell
    (data : WitnessEntry.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value) :
    current.memory statelessRecord = .word record := by
  obtain ⟨caller, previous, previousPost, counts, decoded, sourceEq⟩ := data.origin
  rw [data.prepared]
  change source.memory statelessRecord = .word record
  rw [sourceEq]
  simpa [WitnessRadix.StoreWord.put,
    decoded.context.si_ne_offset input previous pointer statelessRecord record gasWord payloadLength 32 (by decide) (by decide)]
    using decoded.payload_cell

theorem WitnessPrefixFrame.payload_cell
    (data : WitnessPrefixFrame decoderOrigin input current pointer statelessRecord record gasWord requestRecord payloadLength) :
    current.memory statelessRecord = .word record := by
  obtain ⟨origin, prepared, originalPost, value, decoded, memory⟩ := data
  exact (memory statelessRecord (by simpa using WitnessProtected.si_field decoded.context 0 (by decide))).trans decoded.payload_cell

/-- The real offset writes lie in the low SSZ workspace. -/
theorem WitnessValidated.Result.payload_cell
    (data : WitnessValidated.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value) :
    current.memory statelessRecord = .word record := by
  exact data.prefix_frame.payload_cell

/-- The three actual readonly offset loads do not change the pointer cell. -/
theorem WitnessLoaded.Result.payload_cell
    (data : WitnessLoaded.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value) :
    current.memory statelessRecord = .word record := by
  exact data.prefix_frame.payload_cell

/-- Each witness allocation starts after the stateless and payload records. -/
theorem WitnessNodesReturn.Result.payload_cell
    (data : WitnessNodesReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord array payloadLength start length value) :
    current.memory statelessRecord = .word record := by
  exact data.prefix_frame.payload_cell

theorem WitnessCodesReturn.Result.payload_cell
    (data : WitnessCodesReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord nodes codes payloadLength nodeStart nodeLength start length value) :
    current.memory statelessRecord = .word record := by
  exact data.prefix_frame.payload_cell

theorem WitnessHeadersReturn.Result.payload_cell
    (data : WitnessHeadersReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord nodes codes headers payloadLength nodeStart nodeLength codeStart codeLength start length) :
    post.memory statelessRecord = .word record := by
  exact data.prefix_frame.payload_cell

/-- The payload-pointer field is present at the same selected decoder post. -/
theorem WitnessHeadersReturn.Snapshot.payload_cell
    (data : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input post
      pointer statelessRecord record gasWord requestRecord payloadLength) :
    post.memory statelessRecord = .word record := by
  exact data.prefix_frame.payload_cell

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessEntry.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessValidated.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessLoaded.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessNodesReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessCodesReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.payload_cell

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn.Result.earlier_memory
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessPrefixFrame.payload_cell
