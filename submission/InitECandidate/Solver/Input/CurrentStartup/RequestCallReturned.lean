import InitECandidate.Solver.Input.CurrentStartup.WitnessRequestReturn

namespace InitECandidate.Solver.Input.CurrentStartup.RequestCallReturned
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (caller post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) (counts : Nat → BitVec 64) : Prop where
  returned : evaluateHOLFiniteState caller Request.requestsCall = (some (.returned (.val (.word statelessRecord))), post)
  header : WitnessHeadersReturn.Snapshot input post pointer statelessRecord record gasWord requestRecord payloadLength
  decoded : ∃ entry bodyPost start size,
    RequestsReturned.Result input caller entry bodyPost pointer statelessRecord record gasWord requestRecord payloadLength start size counts

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength : Nat, ∃ counts : Nat → BitVec 64,
      Result input caller post pointer statelessRecord record gasWord requestRecord payloadLength counts

/-- Resume the exact normally returned request callee and witness suffix,
then identify the original enclosing call's actual post-state by determinism. -/
theorem witness (input : Guest.InputBlob) (actual : WitnessRequestReturn.Reached input) : Reached input := by
  obtain ⟨caller, source, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, counts, data⟩ := actual
  obtain ⟨entry, bodyPost, start, size, decoded, sourceEq⟩ := data.request.decoded
  obtain ⟨callee, parentPost, parentValue, entryEq, args, called, parentRun⟩ := decoded.origin.invocation
  have normal := parentRun
  rw [Request.requests_shape.2] at normal
  have positive := CallNormal.normal_clock caller parentPost (ofString "rq") .one (ofString "decode_requests")
    Request.requestsArguments Request.afterRequests parentValue normal
  have bodyRun := decoded.returned
  rw [entryEq] at bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact (.val (.word requestRecord) : ValueHOL 64)) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word requestRecord) : ValueHOL 64)) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have resumed := CallNormal.return_execute caller bodyPost "rq" .one (ofString "decode_requests") Request.requestsArguments _
    Requests.body Request.afterRequests callee .one (.val (.word requestRecord)) args called positive bodyRun shapePass
  rw [← sourceEq, data.request.returned] at resumed
  have computed : evaluateHOLFiniteState caller Request.requestsCall =
      (some (.returned (.val (.word statelessRecord))), restore caller "rq" post) := by
    rw [Request.requests_shape.2]
    exact resumed
  have parentEq : parentPost = restore caller "rq" post := congrArg Prod.snd (parentRun.symm.trans computed)
  have parentReturned : evaluateHOLFiniteState caller Request.requestsCall =
      (some (.returned (.val (.word statelessRecord))), parentPost) := by
    rw [parentEq]
    exact computed
  have header := data.header.of_frame (target := parentPost) (by rw [parentEq]; rfl) (by rw [parentEq]; rfl)
  exact ⟨caller, parentPost, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, counts,
    ⟨parentReturned, header, ⟨entry, bodyPost, start, size, decoded⟩⟩⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  witness input (WitnessRequestReturn.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.RequestCallReturned

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallReturned.witness
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallReturned.separated
