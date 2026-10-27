import InitECandidate.Solver.Input.CurrentStartup.HashMetadataReturned

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadSuffixReturned
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

structure Result (input : Guest.InputBlob) (caller source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) : Prop where
  payload : PayloadCallerReturn.Result input caller source post pointer statelessRecord record gasWord payloadLength
    (.val (.word statelessRecord))
  header : WitnessHeadersReturn.Snapshot input post pointer statelessRecord record gasWord requestRecord payloadLength

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller source post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64, ∃ payloadLength : Nat,
    Result input caller source post pointer statelessRecord record gasWord requestRecord payloadLength

/-- The original post-payload continuation ends at this actual returned
witness state, through the true hash-count call's lexical restoration. -/
theorem hash (input : Guest.InputBlob) (actual : HashMetadataReturned.Reached input) : Reached input := by
  obtain ⟨hashSource, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, data⟩ := actual
  obtain ⟨source, count, hashData⟩ := data.hash
  obtain ⟨caller, originalPost, stored, payload, storedRun, endpoint⟩ := hashData.origin
  have snapshot := data.header.of_frame (target := originalPost) (by rw [endpoint]; rfl) (by rw [endpoint]; rfl)
  exact ⟨caller, source, originalPost, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength,
    ⟨payload, snapshot⟩⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  hash input (HashMetadataReturned.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.PayloadSuffixReturned

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadSuffixReturned.hash
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadSuffixReturned.separated
