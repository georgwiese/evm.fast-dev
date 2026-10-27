import InitECandidate.Solver.Input.CurrentStartup.RequestCallReturned

namespace InitECandidate.Solver.Input.CurrentStartup.HashMetadataReturned
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) : Prop where
  returned : evaluateHOLFiniteState source Request.afterHashCount = (some (.returned (.val (.word statelessRecord))), post)
  header : WitnessHeadersReturn.Snapshot input post pointer statelessRecord record gasWord requestRecord payloadLength
  hash : ∃ origin count, HashCountReturn.Result input origin source post pointer statelessRecord record gasWord count
    payloadLength (.val (.word statelessRecord))

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ source post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64, ∃ payloadLength : Nat,
    Result input source post pointer statelessRecord record gasWord requestRecord payloadLength

/-- The real three stateless metadata stores and complete request call retain
the same witness post-state. The original hash-count suffix endpoint is exact. -/
theorem request (input : Guest.InputBlob) (actual : RequestCallReturned.Reached input) : Reached input := by
  obtain ⟨caller, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, counts, data⟩ := actual
  obtain ⟨entry, bodyPost, start, size, decoded⟩ := data.decoded
  obtain ⟨origin, source, hashPost, count, parentValue, first, second, hashData, parentRun, firstRun, secondRun, thirdRun⟩ := decoded.origin.history
  have same := parentRun.symm.trans data.returned
  have valueEq : parentValue = .val (.word statelessRecord) := by
    have result := congrArg Prod.fst same
    cases result
    rfl
  have postEq : hashPost = post := congrArg Prod.snd same
  have firstClock := evaluateHOLFiniteState_clock_le source Request.hashPointerStore
  have secondClock := evaluateHOLFiniteState_clock_le first Request.hashCountStore
  have thirdClock := evaluateHOLFiniteState_clock_le second Request.requestHeaderStore
  rw [firstRun] at firstClock
  rw [secondRun] at secondClock
  rw [thirdRun] at thirdClock
  have returned : evaluateHOLFiniteState source Request.afterHashCount =
      (some (.returned (.val (.word statelessRecord))), hashPost) := by
    rw [Request.requests_shape.1,
      WitnessRadix.StateSteps.next_sequence source first _ _ firstRun firstClock,
      WitnessRadix.StateSteps.next_sequence first second _ _ secondRun secondClock,
      WitnessRadix.StateSteps.next_sequence second caller _ _ thirdRun thirdClock, postEq]
    exact data.returned
  have snapshot := data.header.of_frame (target := hashPost) (by rw [postEq]) (by rw [postEq])
  refine ⟨source, hashPost, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength,
    ⟨returned, snapshot, ⟨origin, count, ?_⟩⟩⟩
  rw [← valueEq]
  exact hashData

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  request input (RequestCallReturned.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.HashMetadataReturned

#print axioms InitECandidate.Solver.Input.CurrentStartup.HashMetadataReturned.request
#print axioms InitECandidate.Solver.Input.CurrentStartup.HashMetadataReturned.separated
