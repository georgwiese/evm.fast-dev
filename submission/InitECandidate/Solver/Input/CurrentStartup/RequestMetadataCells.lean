import InitECandidate.Solver.Input.CurrentStartup.RequestsEntry
import InitECandidate.Solver.Input.CurrentStartup.CallerSiBase

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
variable {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
variable {source current post caller entry : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {pointer statelessRecord record gasWord count : BitVec 64}
variable {length payloadLength start size : Nat} {value : ValueHOL 64}

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
theorem RequestsEntry.Result.metadata
    (data : RequestsEntry.Result (decoderOrigin := decoderOrigin) input caller entry post
      pointer statelessRecord record gasWord payloadLength start size value) :
    caller.memory statelessRecord = .word record ∧
    caller.memory (statelessRecord + 8#64) = .word (pointer + 18#64 + Request.requestWords input 1) ∧
    caller.memory (statelessRecord + 16#64) = .word (BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32)) ∧
    caller.memory (statelessRecord + 24#64) = .word (pointer + 18#64 + 8#64) := by
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
  refine ⟨thirdKept.trans (secondKept.trans (kept.trans hashes.payload_cell)), ?_⟩
  have countEq : count = BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32) := by
    rw [← hashes.countEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [callerEq, secondEq, firstEq]
  simp [WitnessRadix.StoreWord.put,
    context.si_fields_ne input hashSource pointer statelessRecord record gasWord payloadLength 8 24 (by decide) (by decide) (by decide),
    context.si_fields_ne input hashSource pointer statelessRecord record gasWord payloadLength 8 16 (by decide) (by decide) (by decide),
    context.si_fields_ne input hashSource pointer statelessRecord record gasWord payloadLength 16 24 (by decide) (by decide) (by decide), countEq]

theorem RequestsEntry.Result.payload_cell
    (data : RequestsEntry.Result (decoderOrigin := decoderOrigin) input caller entry post
      pointer statelessRecord record gasWord payloadLength start size value) :
    caller.memory statelessRecord = .word record := data.metadata.1

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.HashCountReturn.Result.payload_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsEntry.Result.metadata
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsEntry.Result.payload_cell
