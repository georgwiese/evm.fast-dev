import InitECandidate.Solver.Input.CurrentStartup.PayloadCallReturned

namespace InitECandidate.Solver.Input.CurrentStartup.StatelessReturned
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The physical witness snapshot belongs to this particular original
stateless decoder return, not merely another normal run for the same input. -/
theorem rooted (origin : DecoderOrigin) (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input origin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ record gasWord requestRecord : BitVec 64, ∃ payloadLength : Nat,
      WitnessHeadersReturn.Snapshot (decoderOrigin := origin) input origin.post origin.pointer origin.word
        record gasWord requestRecord payloadLength := by
  obtain ⟨caller, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, data⟩ :=
    PayloadCallReturned.separated input actual gas
  obtain ⟨entry, bodyPost, callee, decoded, invocation⟩ := data.decoded
  obtain ⟨entryEq, lower, aligned, room, si, heap, locals, args, called, returned, rootFrame⟩ := invocation
  have pointerEq : pointer = origin.pointer := rootFrame.pointer
  have wordEq : statelessRecord = origin.word :=
    HolWordLab.word.inj (ValueHOL.val.inj rootFrame.value)
  have snapshot := data.header.of_frame (target := origin.post) rootFrame.state.symm rootFrame.clock.symm
  rw [pointerEq, wordEq] at snapshot
  exact ⟨record, gasWord, requestRecord, payloadLength, snapshot⟩

/-- Explicit physical projections at the same original post-state: bounded
payload gas, copied input, bounded heap and all three actual witness arrays. -/
theorem physical (origin : DecoderOrigin) (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input origin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ record gasWord requestRecord nodes codes headers : BitVec 64,
    ∃ payloadLength nodeStart nodeLength codeStart codeLength start length : Nat,
      gasWord.toNat ≤ 200000000 ∧ origin.post.memory (record + 88#64) = .word gasWord ∧
      Blob.HeapInput origin.post input origin.pointer ∧
      NormalHeapEffects.AtLeast (max (record.toNat + 136) (requestRecord.toNat + 80)) origin.post ∧
      VarList.Records origin.post input origin.pointer nodes nodeStart nodeLength ∧
      VarList.Records origin.post input origin.pointer codes codeStart codeLength ∧
      VarList.Records origin.post input origin.pointer headers start length ∧
      VarList.decodedCount input start length ≤ 256 := by
  obtain ⟨record, gasWord, requestRecord, payloadLength, snapshot⟩ := rooted origin input actual gas
  obtain ⟨headerSource, ready, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    start, length, data, frame, clock⟩ := snapshot
  have memory : origin.post.memory = headerPost.memory := by
    have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) frame
    exact same
  have globals : origin.post.globals = headerPost.globals := by
    have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) frame
    exact same
  have domain : origin.post.memaddrs = headerPost.memaddrs := by
    have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) frame
    exact same
  have endian : origin.post.be = headerPost.be := by
    have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) frame
    exact same
  have postHeap : NormalHeapEffects.AtLeast (max (record.toNat + 136) (requestRecord.toNat + 80)) origin.post := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := data.heap
    exact ⟨cursor, (congrArg (fun table => table.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr")) globals).trans cell,
      low, high, aligned⟩
  refine ⟨record, gasWord, requestRecord, nodes, codes, headers, payloadLength, nodeStart, nodeLength, codeStart, codeLength,
    start, length, data.context.gasBound, ?_, ?_, postHeap,
    VarList.Records.of_memory headerPost origin.post input origin.pointer nodes nodeStart nodeLength memory data.nodeRecords,
    VarList.Records.of_memory headerPost origin.post input origin.pointer codes codeStart codeLength memory data.codeRecords,
    VarList.Records.of_memory headerPost origin.post input origin.pointer headers start length memory data.headerRecords, data.headerCountBound⟩
  · rw [memory]
    exact data.gas
  · exact Blob.HeapInput.of_fields headerPost origin.post input origin.pointer memory.symm domain.symm endian.symm data.image

end InitECandidate.Solver.Input.CurrentStartup.StatelessReturned

#print axioms InitECandidate.Solver.Input.CurrentStartup.StatelessReturned.rooted
#print axioms InitECandidate.Solver.Input.CurrentStartup.StatelessReturned.physical
