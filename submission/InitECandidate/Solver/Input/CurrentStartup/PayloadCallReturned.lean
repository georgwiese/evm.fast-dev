import InitECandidate.Solver.Input.CurrentStartup.PayloadSuffixReturned

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadCallReturned
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (caller post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) : Prop where
  returned : evaluateHOLFiniteState caller Request.continuation = (some (.returned (.val (.word statelessRecord))), post)
  header : WitnessHeadersReturn.Snapshot input post pointer statelessRecord record gasWord requestRecord payloadLength
  decoded : ∃ entry bodyPost, PayloadEntry.Result input entry bodyPost pointer payloadLength (.val (.word record))

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64, ∃ payloadLength : Nat,
    Result input caller post pointer statelessRecord record gasWord requestRecord payloadLength

/-- The complete actual payload call, request metadata/decoder, witness lists
and return share this original enclosing call's exact physical post-state. -/
theorem suffix (input : Guest.InputBlob) (actual : PayloadSuffixReturned.Reached input) : Reached input := by
  obtain ⟨caller, source, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, data⟩ := actual
  obtain ⟨entry, bodyPost, callee, parentPost, parentValue, decoded, bodyRun, entryEq, args, called, parentRun, sourceEq⟩ := data.payload.payload
  have normal := parentRun
  rw [Request.payload_call_shape] at normal
  have positive := CallNormal.normal_clock caller parentPost (ofString "pl") .one (ofString "decode_payload")
    Request.payloadArguments Request.afterPayload parentValue normal
  rw [entryEq] at bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact (.val (.word record) : ValueHOL 64)) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word record) : ValueHOL 64)) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have resumed := CallNormal.return_execute caller bodyPost "pl" .one (ofString "decode_payload") Request.payloadArguments _
    Payload.body Request.afterPayload callee .one (.val (.word record)) args called positive bodyRun shapePass
  rw [← sourceEq, data.payload.returned] at resumed
  have computed : evaluateHOLFiniteState caller Request.continuation =
      (some (.returned (.val (.word statelessRecord))), restore caller "pl" post) := by
    rw [Request.payload_call_shape]
    exact resumed
  have parentEq : parentPost = restore caller "pl" post := congrArg Prod.snd (parentRun.symm.trans computed)
  have parentReturned : evaluateHOLFiniteState caller Request.continuation =
      (some (.returned (.val (.word statelessRecord))), parentPost) := by
    rw [parentEq]
    exact computed
  have snapshot := data.header.of_frame (target := parentPost) (by rw [parentEq]; rfl) (by rw [parentEq]; rfl)
  exact ⟨caller, parentPost, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength,
    ⟨parentReturned, snapshot, ⟨entry, bodyPost, decoded⟩⟩⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  suffix input (PayloadSuffixReturned.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.PayloadCallReturned

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallReturned.suffix
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallReturned.separated
