import InitECandidate.Solver.Input.CurrentStartup.RequestTransactions
import InitECandidate.Solver.Input.CurrentStartup.DecodedPayloadPointer

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
variable {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
variable {source current post caller : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {pointer statelessRecord record gasWord requestRecord : BitVec 64}
variable {payloadLength : Nat} {counts : Nat → BitVec 64} {value : ValueHOL 64}

/-- The actual request allocation starts after the complete transaction array.
The request return therefore retains its cells and both payload output fields. -/
theorem RequestCallerReturn.Result.transactions
    (data : RequestCallerReturn.Result (decoderOrigin := decoderOrigin) input caller current post
      pointer statelessRecord record gasWord requestRecord payloadLength counts value) :
    ∃ array start size, Payload.TransactionImage input current pointer record array start size ∧
      array.toNat + 16 * VarList.decodedCount input start size ≤ requestRecord.toNat := by
  obtain ⟨entry, bodyPost, start, size, decoded, currentEq⟩ := data.decoded
  obtain ⟨array, txStart, txSize, transactions⟩ := decoded.origin.transactions
  have before : array.toNat + 16 * VarList.decodedCount input txStart txSize ≤ requestRecord.toNat := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := transactions.heapExtent
    have same : cursor = requestRecord := by
      have eq := Option.some.inj (cell.symm.trans decoded.callerHeap)
      cases eq
      rfl
    subst cursor
    exact low
  have heap : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input txStart txSize) current := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := data.heap
    exact ⟨cursor, cell, by omega, high, aligned⟩
  refine ⟨array, txStart, txSize, transactions.of_interval requestRecord.toNat before ?_ heap, before⟩
  intro query lower upper
  apply data.earlier_memory query _ upper
  have := data.context.recordAfter
  omega

/-- The real SI32 store and witness declarations preserve the array before rq. -/
theorem WitnessEntry.Result.transactions
    (data : WitnessEntry.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord requestRecord payloadLength value) :
    ∃ array start size, Payload.TransactionImage input current pointer record array start size ∧
      array.toNat + 16 * VarList.decodedCount input start size ≤ requestRecord.toNat := by
  obtain ⟨caller, previous, previousPost, counts, decoded, sourceEq⟩ := data.origin
  obtain ⟨array, start, size, transactions, before⟩ := decoded.transactions
  have beforeSi : (statelessRecord + 32#64).toNat < record.toNat := by
    rw [decoded.context.si_field_number input previous pointer statelessRecord record gasWord payloadLength 32 (by decide)]
    have := decoded.context.recordAfter
    omega
  have sourceImage : Payload.TransactionImage input source pointer record array start size := by
    rw [sourceEq]
    exact transactions.store_before (statelessRecord + 32#64) requestRecord beforeSi
  exact ⟨array, start, size, sourceImage.of_frame (by rw [data.prepared]; rfl), before⟩

/-- The final selected snapshot retains the real bounded allocator frontier. -/
theorem WitnessHeadersReturn.Snapshot.heap
    (snapshot : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input current
      pointer statelessRecord record gasWord requestRecord payloadLength) :
    NormalHeapEffects.AtLeast (max (record.toNat + 136) (requestRecord.toNat + 80)) current := by
  obtain ⟨headerSource, ready, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    start, length, data, frame, clock⟩ := snapshot
  have globals := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) frame
  obtain ⟨cursor, cell, low, high, aligned⟩ := data.heap
  exact ⟨cursor, (congrArg (fun table => table.lookup (ofString "heap_ptr")) globals).trans cell, low, high, aligned⟩

/-- Complete transaction records and their real pointer/count fields survive
all three witness decoders at the same selected stateless post-state. -/
theorem WitnessHeadersReturn.Snapshot.transactions
    (snapshot : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input current
      pointer statelessRecord record gasWord requestRecord payloadLength) :
    ∃ array start size, Payload.TransactionImage input current pointer record array start size ∧
      array.toNat + 16 * VarList.decodedCount input start size ≤ requestRecord.toNat := by
  obtain ⟨origin, prepared, originalPost, value, decoded, memory⟩ := snapshot.prefix_frame
  obtain ⟨array, start, size, transactions, before⟩ := decoded.transactions
  have heap : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start size) current := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := snapshot.heap
    exact ⟨cursor, cell, by omega, high, aligned⟩
  refine ⟨array, start, size, transactions.of_interval (max (record.toNat + 136) (requestRecord.toNat + 80))
    (by omega) ?_ heap, before⟩
  intro query lower upper
  apply memory query
  refine ⟨by have := decoded.context.recordAfter; omega, upper, ?_⟩
  intro offset member same
  have small : offset ≤ 80 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have number := decoded.context.si_field_number input prepared pointer statelessRecord record gasWord payloadLength offset (by omega)
  rw [same, number] at lower
  have := decoded.context.recordAfter
  omega

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn.Result.transactions
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessEntry.Result.transactions
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.heap
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.transactions
