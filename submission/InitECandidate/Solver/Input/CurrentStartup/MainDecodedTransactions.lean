import InitECandidate.Solver.Input.CurrentStartup.DecodedTransactions
import InitECandidate.Solver.Input.CurrentStartup.MainDecodedState
import InitECandidate.Solver.Input.VarList.RecordSizes
import InitECandidate.Solver.Input.VarList.RecordsInputBound

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Real input bytes and16-byte transaction records share the finite persistent
arena. This is derived from the same complete decoder return, not a new input
restriction or allocation-success premise. -/
theorem WitnessHeadersReturn.Snapshot.transactions_bounded
    {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
    {post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer statelessRecord record gasWord requestRecord : BitVec 64} {payloadLength : Nat}
    (snapshot : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input post
      pointer statelessRecord record gasWord requestRecord payloadLength) :
    ∃ array start size, Payload.TransactionImage input post pointer record array start size ∧
      array.toNat + 16 * VarList.decodedCount input start size ≤ requestRecord.toNat ∧
      input.length % 2^64 + 16 * VarList.decodedCount input start size ≤ 251655056 ∧
      VarList.decodedCount input start size ≤ 12582752 ∧
      VarList.sumPrefix (fun index => (VarList.recordLength input start size (VarList.decodedCount input start size) index).toNat)
        (VarList.decodedCount input start size) ≤ 251655056 := by
  obtain ⟨array, start, size, transactions, before⟩ := snapshot.transactions
  obtain ⟨headerSource, ready, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    headerStart, headerLength, data, frame, clock⟩ := snapshot
  have budget : input.length % 2^64 + 16 * VarList.decodedCount input start size ≤ 251655056 := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := data.heap
    have := data.context.pointerLower
    have := data.context.statelessLower
    have := data.context.recordAfter
    have := transactions.arrayAfter
    omega
  have countBound := VarList.Records.count_input_bound post input pointer array start size transactions.records
  have sizes := VarList.Records.size_bounds post input pointer array start size transactions.records
  exact ⟨array, start, size, transactions, before, budget, by omega, by have := transactions.inside; omega⟩

/-- The whole actual main decoder continuation retains the original
transaction records, real pointer/count fields, and uniform count/byte bounds. -/
theorem MainDecodedState.transactions
    {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : HostState input source) (heap : NormalHeapEffects.AtLeast 2701134640 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (execution : CallPrefix.Execution source DecoderPrefix.actions target)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ origin : DecoderOrigin, ∃ record gasWord requestRecord array : BitVec 64,
    ∃ payloadLength start size : Nat,
      MainSeparatedInput.RootRun input origin ∧
      target.locals.lookup (ofString "si") = some (.val (.word origin.word)) ∧
      WitnessHeadersReturn.Snapshot (decoderOrigin := origin) input target origin.pointer origin.word record gasWord requestRecord payloadLength ∧
      Payload.TransactionImage input target origin.pointer record array start size ∧
      input.length % 2^64 + 16 * VarList.decodedCount input start size ≤ 251655056 ∧
      VarList.decodedCount input start size ≤ 12582752 ∧
      VarList.sumPrefix (fun index => (VarList.recordLength input start size (VarList.decodedCount input start size) index).toNat)
        (VarList.decodedCount input start size) ≤ 251655056 := by
  obtain ⟨origin, record, gasWord, requestRecord, payloadLength, run, si, snapshot⟩ :=
    MainDecodedState.current initial heap offsets execution gas
  obtain ⟨array, start, size, transactions, before, budget, countBound, byteBound⟩ := snapshot.transactions_bounded
  exact ⟨origin, record, gasWord, requestRecord, array, payloadLength, start, size, run, si, snapshot,
    transactions, budget, countBound, byteBound⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.transactions_bounded
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedState.transactions
