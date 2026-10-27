import InitECandidate.Solver.Input.CurrentStartup.WitnessSnapshot

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessRequestReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The witness arrays belong to this actual request-caller post-state,
including every intervening lexical restoration and the earlier rq store. -/
structure Result (input : Guest.InputBlob) (caller source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) (counts : Nat → BitVec 64) : Prop where
  request : RequestCallerReturn.Result input caller source post pointer statelessRecord record gasWord requestRecord
    payloadLength counts (.val (.word statelessRecord))
  header : WitnessHeadersReturn.Snapshot input post pointer statelessRecord record gasWord requestRecord payloadLength

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller source post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength : Nat, ∃ counts : Nat → BitVec 64,
      Result input caller source post pointer statelessRecord record gasWord requestRecord payloadLength counts

/-- Rewind the actual header/code/node calls, offset loads, validator and
witness declarations to the same original request-caller execution. -/
theorem headers (input : Guest.InputBlob) (actual : WitnessHeadersReturn.Reached input) : Reached input := by
  obtain ⟨headerSource, ready, headerPost, pointer, statelessRecord, record, gasWord, requestRecord, nodes, codes, headerArray,
    payloadLength, nodeStart, nodeLength, codeStart, codeLength, start, length, data⟩ := actual
  obtain ⟨codeOrigin, codeData⟩ := data.origin
  obtain ⟨nodeOrigin, codeParentPost, nodeData, codeEndpoint⟩ := codeData.origin
  obtain ⟨loadOrigin, nodeParentPost, loadedData, nodeEndpoint⟩ := nodeData.origin
  obtain ⟨valOrigin, loadedParentPost, validatedData, loadedFrame, loadedClock⟩ := loadedData.endpoint
  obtain ⟨witnessCaller, entryParentPost, entryData, entryFrame, entryClock⟩ := validatedData.endpoint
  obtain ⟨prefixPost, prefixRun, prefixClock, prefixFrame⟩ := entryData.endpoint
  obtain ⟨caller, source, post, counts, requestData, witnessSource⟩ := entryData.origin
  obtain ⟨stored, context⟩ := requestData.context.stateless_store input source pointer statelessRecord record gasWord payloadLength 32
    (localVar "rq") requestRecord (by decide) (by decide) (Request.local_word source "rq" requestRecord requestData.rq)
  let entered := {source with memory := WitnessRadix.StoreWord.put source.memory (statelessRecord + 32#64) requestRecord}
  have requestRun := requestData.returned
  rw [WitnessEntry.source_shape, WitnessRadix.StateSteps.next_sequence source entered _ _ stored (Nat.le_refl _)] at requestRun
  have sourceEq : witnessCaller = entered := witnessSource
  rw [← sourceEq] at requestRun
  have postEq : post = prefixPost := congrArg Prod.snd (requestRun.symm.trans prefixRun)
  have scopesFrame : LocalEffects.erase nodeParentPost = LocalEffects.erase headerPost := by
    rw [nodeEndpoint, codeEndpoint]
    rfl
  have scopesClock : nodeParentPost.clock = headerPost.clock := by
    rw [nodeEndpoint, codeEndpoint]
    rfl
  have frame : LocalEffects.erase post = LocalEffects.erase headerPost := by
    rw [postEq]
    exact prefixFrame.trans (entryFrame.trans (loadedFrame.trans scopesFrame))
  have clock : post.clock = headerPost.clock := by
    rw [postEq]
    exact prefixClock.trans (entryClock.trans (loadedClock.trans scopesClock))
  exact ⟨caller, source, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, counts,
    ⟨requestData, ⟨headerSource, ready, headerPost, nodes, codes, headerArray, nodeStart, nodeLength, codeStart, codeLength,
      start, length, data, frame, clock⟩⟩⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  headers input (WitnessHeadersReturn.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.WitnessRequestReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessRequestReturn.headers
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessRequestReturn.separated
