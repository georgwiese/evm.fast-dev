import InitECandidate.Solver.Input.CurrentStartup.WitnessSnapshot
import InitECandidate.Solver.Input.CurrentStartup.CallerSiBase

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
variable {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
variable {source current post caller entry : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {pointer statelessRecord record gasWord count requestRecord array nodes codes headers : BitVec 64}
variable {length payloadLength start size nodeStart nodeLength codeStart codeLength : Nat}
variable {value : ValueHOL 64} {counts : Nat → BitVec 64}

/-- The actual payload-pointer store, followed by the readonly count call. -/
theorem HashCountReturn.Result.payload_cell
    (data : HashCountReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord count length value) :
    current.memory statelessRecord = .word record := by
  obtain ⟨origin, originalPost, stored, previous, storedRun, frame, endpoint⟩ := data.origin
  have context := previous.context
  obtain ⟨run, storedContext⟩ := context.stateless_store input source pointer statelessRecord record gasWord length 0
    (localVar "pl") record (by decide) (by decide) (Request.local_word source "pl" record context.pl)
  change evaluateHOLFiniteState source Request.payloadPointerStore = _ at run
  have same := congrArg Prod.snd (storedRun.symm.trans run)
  dsimp only at same
  have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) frame
  change current.memory = stored.memory at memory
  rw [memory, same]
  simp [WitnessRadix.StoreWord.put]

/-- The three genuine metadata stores are all above the payload-pointer cell. -/
theorem RequestsEntry.Result.payload_cell
    (data : RequestsEntry.Result (decoderOrigin := decoderOrigin) input caller entry post
      pointer statelessRecord record gasWord payloadLength start size value) :
    caller.memory statelessRecord = .word record := by
  obtain ⟨origin, hashSource, hashPost, count, parentValue, first, second, hashes, callerRun,
    firstRun, secondRun, thirdRun⟩ := data.history
  have context := hashes.context
  have firstRead : eval hashSource (.op .add [localVar "np", localVar "o_vh"]) =
      some (.val (.word (pointer + 18#64 + Request.requestWords input 1))) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, context.request.np, context.request.vh,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨run, nextContext, kept⟩ := context.store_base input hashSource pointer statelessRecord record gasWord payloadLength 8
    (.op .add [localVar "np", localVar "o_vh"]) _ (by decide) (by decide) (by decide) firstRead
  change evaluateHOLFiniteState hashSource Request.hashPointerStore = _ at run
  have firstEq := congrArg Prod.snd (firstRun.symm.trans run)
  dsimp only at firstEq
  rw [← firstEq] at nextContext kept
  have countCell : first.locals.lookup (ofString "nvh") = some (.val (.word count)) := by
    rw [firstEq]
    exact hashes.nvh
  obtain ⟨run, finalContext, secondKept⟩ := nextContext.store_base input first pointer statelessRecord record gasWord payloadLength 16
    (localVar "nvh") count (by decide) (by decide) (by decide) (Request.local_word first "nvh" count countCell)
  change evaluateHOLFiniteState first Request.hashCountStore = _ at run
  have secondEq := congrArg Prod.snd (secondRun.symm.trans run)
  dsimp only at secondEq
  rw [← secondEq] at finalContext secondKept
  have headerRead := Scalar.plus_read second (localVar "np") (pointer + 18#64) 8
    (Request.local_word second "np" _ finalContext.request.np)
  obtain ⟨run, callerContext, thirdKept⟩ := finalContext.store_base input second pointer statelessRecord record gasWord payloadLength 24
    (Scalar.plus (localVar "np") 8) _ (by decide) (by decide) (by decide) headerRead
  change evaluateHOLFiniteState second Request.requestHeaderStore = _ at run
  have callerEq := congrArg Prod.snd (thirdRun.symm.trans run)
  dsimp only at callerEq
  rw [← callerEq] at thirdKept
  exact thirdKept.trans (secondKept.trans (kept.trans hashes.payload_cell))

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
  have outside : 2701132528 + 40 ≤ statelessRecord.toNat := by
    have := context.statelessLower
    have := context.pointerLower
    omega
  have memory := decoded.memory statelessRecord before (Or.inr outside)
  obtain ⟨callee, parentPost, parentValue, entryEq, rest⟩ := decoded.origin.invocation
  have entryCell : entry.memory statelessRecord = caller.memory statelessRecord := by rw [entryEq]; rfl
  rw [currentEq]
  exact memory.trans (entryCell.trans decoded.origin.payload_cell)

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

/-- The real offset writes lie in the low SSZ workspace. -/
theorem WitnessValidated.Result.payload_cell
    (data : WitnessValidated.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value) :
    current.memory statelessRecord = .word record := by
  obtain ⟨caller, originalPost, decoded, frame, clock, memory⟩ := data.endpoint
  have outside : 2701132528 + 24 ≤ statelessRecord.toNat := by
    have := data.context.statelessLower
    have := data.context.pointerLower
    omega
  exact (memory statelessRecord (Or.inr outside)).trans decoded.payload_cell

/-- The three actual readonly offset loads do not change the pointer cell. -/
theorem WitnessLoaded.Result.payload_cell
    (data : WitnessLoaded.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value) :
    current.memory statelessRecord = .word record := by
  obtain ⟨origin, originalPost, decoded, frame, clock⟩ := data.endpoint
  rw [data.prepared]
  exact decoded.payload_cell

/-- Each witness allocation starts after the stateless and payload records. -/
theorem WitnessNodesReturn.Result.payload_cell
    (data : WitnessNodesReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord array payloadLength start length value) :
    current.memory statelessRecord = .word record := by
  obtain ⟨origin, originalPost, decoded, endpoint⟩ := data.origin
  have before : statelessRecord.toNat < array.toNat := by
    have := data.arrayAfter
    have := data.context.recordAfter
    omega
  exact (data.memory statelessRecord before
    (data.context.si_ne_offset input current pointer statelessRecord record gasWord payloadLength 40 (by decide) (by decide))
    (data.context.si_ne_offset input current pointer statelessRecord record gasWord payloadLength 48 (by decide) (by decide))).trans decoded.payload_cell

theorem WitnessCodesReturn.Result.payload_cell
    (data : WitnessCodesReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord nodes codes payloadLength nodeStart nodeLength start length value) :
    current.memory statelessRecord = .word record := by
  obtain ⟨origin, originalPost, decoded, endpoint⟩ := data.origin
  have before : statelessRecord.toNat < codes.toNat := by
    have := data.arrayAfter
    have := data.context.recordAfter
    omega
  exact (data.memory statelessRecord before
    (data.context.si_ne_offset input current pointer statelessRecord record gasWord payloadLength 56 (by decide) (by decide))
    (data.context.si_ne_offset input current pointer statelessRecord record gasWord payloadLength 64 (by decide) (by decide))).trans decoded.payload_cell

theorem WitnessHeadersReturn.Result.payload_cell
    (data : WitnessHeadersReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord nodes codes headers payloadLength nodeStart nodeLength codeStart codeLength start length) :
    post.memory statelessRecord = .word record := by
  obtain ⟨origin, decoded⟩ := data.origin
  have before : statelessRecord.toNat < headers.toNat := by
    have := data.arrayAfter
    have := data.context.recordAfter
    omega
  exact (data.memory statelessRecord before
    (data.context.si_ne_offset input current pointer statelessRecord record gasWord payloadLength 72 (by decide) (by decide))
    (data.context.si_ne_offset input current pointer statelessRecord record gasWord payloadLength 80 (by decide) (by decide))).trans decoded.payload_cell

/-- The payload-pointer field is present at the same selected decoder post. -/
theorem WitnessHeadersReturn.Snapshot.payload_cell
    (data : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input post
      pointer statelessRecord record gasWord requestRecord payloadLength) :
    post.memory statelessRecord = .word record := by
  obtain ⟨headerSource, ready, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    start, length, decoded, frame, clock⟩ := data
  have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) frame
  change post.memory = headerPost.memory at memory
  rw [memory]
  exact decoded.payload_cell

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.HashCountReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsEntry.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessEntry.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessValidated.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessLoaded.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessNodesReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessCodesReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.payload_cell
