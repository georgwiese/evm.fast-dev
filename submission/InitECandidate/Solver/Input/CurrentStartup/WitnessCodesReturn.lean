import InitECandidate.Solver.Input.CurrentStartup.WitnessNodesReturn

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessCodesReturn
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord nodes codes : BitVec 64)
    (payloadLength nodeStart nodeLength start length : Nat) (value : ValueHOL 64) : Prop where
  startEq : start = 2 + Guest.GasLimit.le32 input 6 + Witness.offsetNat input (2 + Guest.GasLimit.le32 input 6) 1
  lengthEq : length = Witness.offsetNat input (2 + Guest.GasLimit.le32 input 6) 2 - Witness.offsetNat input (2 + Guest.GasLimit.le32 input 6) 1
  inside : start + length ≤ input.length % 2^64
  context : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength
  heap : NormalHeapEffects.AtLeast (max (record.toNat + 136) (requestRecord.toNat + 80)) current
  arrayAfter : max (record.toNat + 136) (requestRecord.toNat + 80) ≤ codes.toNat
  nodesBefore : nodes.toNat + 16 * VarList.decodedCount input nodeStart nodeLength ≤ codes.toNat
  heapExtent : NormalHeapEffects.AtLeast (codes.toNat + 16 * VarList.decodedCount input start length) current
  nodeRecords : VarList.Records current input pointer nodes nodeStart nodeLength
  codeRecords : VarList.Records current input pointer codes start length
  nodeLengths : ∀ index < VarList.decodedCount input nodeStart nodeLength,
    (VarList.recordLength input nodeStart nodeLength (VarList.decodedCount input nodeStart nodeLength) index).toNat ≤ 1024
  codeLengths : ∀ index < VarList.decodedCount input start length,
    (VarList.recordLength input start length (VarList.decodedCount input start length) index).toNat ≤ 65536
  codePointer : current.memory (statelessRecord + 56#64) = .word (VarList.decodedArray codes length)
  codeCount : current.memory (statelessRecord + 64#64) = .word (BitVec.ofNat 64 (VarList.decodedCount input start length))
  live : WitnessLive input current pointer
  memory : ∀ query : BitVec 64, query.toNat < codes.toNat →
    query ≠ statelessRecord + 56#64 → query ≠ statelessRecord + 64#64 → current.memory query = source.memory query
  price : source.clock - current.clock ≤ 2 * (length / 4) + 3
  clock : current.clock ≤ source.clock
  returned : evaluateHOLFiniteState current Witness.headerCall = (some (.returned value), post)
  origin : ∃ original originalPost, WitnessNodesReturn.Result (decoderOrigin := decoderOrigin) input original source originalPost
    pointer statelessRecord record gasWord requestRecord nodes payloadLength nodeStart nodeLength value ∧
    originalPost = restore source "cd" post

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ source current post, ∃ pointer statelessRecord record gasWord requestRecord nodes codes : BitVec 64,
    ∃ payloadLength nodeStart nodeLength start length : Nat, ∃ value : ValueHOL 64,
      Result (decoderOrigin := decoderOrigin) input source current post pointer statelessRecord record gasWord requestRecord nodes codes
        payloadLength nodeStart nodeLength start length value

/-- The second genuine witness-list call and both si stores, preserving the
previous node records and deriving the65536-byte code-item limit. -/
theorem nodes (input : Guest.InputBlob) (actual : WitnessNodesReturn.Reached (decoderOrigin := decoderOrigin) input) : Reached (decoderOrigin := decoderOrigin) input := by
  classical
  obtain ⟨original, source, post, pointer, statelessRecord, record, gasWord, requestRecord, nodeArray, payloadLength,
    nodeStart, nodeLength, value, data⟩ := actual
  let witnessStart := 2 + Guest.GasLimit.le32 input 6
  let first := Witness.offsetNat input witnessStart 1
  let last := Witness.offsetNat input witnessStart 2
  let total := input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6
  let start := witnessStart + first
  let length := last - first
  have live := data.live
  obtain ⟨oldSource, oldPost, initial, oldEndpoint⟩ := data.origin
  have values := Witness.offset_values input witnessStart (BitVec.ofNat 64 total) initial.first initial.valid
  have totalNat : (BitVec.ofNat 64 total).toNat = total := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.mod_lt input.length (show 0 < 2^64 by decide); dsimp [total]; omega)]
  rw [totalNat] at values
  have outer := data.context.request.outer
  obtain ⟨inside, args⟩ := WitnessSlices.arguments_between input source pointer first last 9223372036854775807 65536 "w1" "w2"
    (by have := outer.lower; have := outer.upper; omega) outer.upper values.2.2.1 values.2.2.2 live.wp live.w1 live.w2
  have normal := data.returned
  rw [Witness.arrays_shape.2.2.1] at normal
  let base := max (record.toNat + 136) (requestRecord.toNat + 80)
  let floor := max base (nodeArray.toNat + 16 * VarList.decodedCount input nodeStart nodeLength)
  obtain ⟨decoded, inner, array, context, heap, heapExtent, locals, records, countLimit, lengths,
    memory, arrayLower, arrayAligned, arrayBound, forward, price, remaining, endpoint⟩ :=
    ByteListCall.normal input source post pointer statelessRecord record gasWord 9223372036854775807#64 65536#64
      payloadLength start length floor data.context (data.heap.maximum data.heapExtent) (by dsimp [floor, base]; omega) inside
      "cd" _ Witness.afterCode (by decide) args value normal
  have nodesBefore : nodeArray.toNat + 16 * VarList.decodedCount input nodeStart nodeLength ≤ array.toNat := by
    dsimp [floor] at arrayLower
    omega
  have oldRecords := VarList.Records.of_before source decoded input pointer nodeArray nodeStart nodeLength array.toNat
    data.records nodesBefore memory
  have countFacts := VarList.Records.cells decoded input pointer array start length context.domain records
  let count := BitVec.ofNat 64 (VarList.decodedCount input start length)
  have countNat : count.toNat = VarList.decodedCount input start length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := countFacts.2.1; omega)]
  have tuple : decoded.locals.lookup (ofString "cd") =
      some (VarList.pairValue (VarList.decodedArray array length) count.toNat) := by
    rw [locals, countNat]
    simp [HolFiniteMapExact.update, FUPDATE, BytesList.pairValue]
  have arena : WitnessRadix.AllocatedBytes.Arena statelessRecord 96 :=
    ⟨by have := context.pointerLower; have := context.statelessLower; omega, by have := context.statelessRoom; omega⟩
  obtain ⟨stores, firstCell, secondCell, frame⟩ := Witness.pair_stores decoded statelessRecord
    (VarList.decodedArray array length) count "cd" 56 Witness.headerCall context.si tuple context.domain arena
    context.statelessAligned (by decide) (by decide)
  let current := Witness.pairStored decoded statelessRecord 56 (VarList.decodedArray array length) count
  have currentContext := context.pair_stores input decoded pointer statelessRecord record gasWord
    (VarList.decodedArray array length) count payloadLength 56 "cd" (by decide) (by decide) tuple
  have siBefore : statelessRecord.toNat + 96 ≤ array.toNat := by
    have := context.recordAfter
    dsimp [floor, base] at arrayLower
    omega
  have currentRecords := Witness.records_after_pair_stores decoded input pointer array statelessRecord
    (VarList.decodedArray array length) count start length 56 records arena (by decide) siBefore
  have currentNodes := Witness.records_after_pair_stores decoded input pointer nodeArray statelessRecord
    (VarList.decodedArray array length) count nodeStart nodeLength 56 oldRecords arena (by decide) (by
      have := context.recordAfter
      have := data.arrayAfter
      omega)
  have currentLive : WitnessLive input current pointer := live.preserved (by
    intro name member
    change decoded.locals.lookup (ofString name) = source.locals.lookup (ofString name)
    rw [locals]
    have different : ofString "cd" ≠ ofString name := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    simp [HolFiniteMapExact.update, FUPDATE, different])
  have currentHeap : NormalHeapEffects.AtLeast base current := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := heap
    exact ⟨cursor, cell, by dsimp [floor] at low; omega, high, aligned⟩
  have run := remaining
  rw [Witness.arrays_shape.2.2.2.1, stores] at run
  exact ⟨source, current, inner, pointer, statelessRecord, record, gasWord, requestRecord, nodeArray, array,
    payloadLength, nodeStart, nodeLength, start, length, value,
    ⟨rfl, rfl, inside, currentContext, currentHeap, by dsimp [floor] at arrayLower; omega,
      nodesBefore, heapExtent, currentNodes, currentRecords, data.lengths, lengths, firstCell, secondCell, currentLive,
      (fun query before firstAway secondAway => (frame query firstAway secondAway).trans (memory query before)),
      price, forward, run, ⟨original, post, data, endpoint⟩⟩⟩

theorem separated (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached (decoderOrigin := decoderOrigin) input :=
  nodes input (WitnessNodesReturn.separated input actual gas)

end InitECandidate.Solver.Input.CurrentStartup.WitnessCodesReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessCodesReturn.nodes
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessCodesReturn.separated
