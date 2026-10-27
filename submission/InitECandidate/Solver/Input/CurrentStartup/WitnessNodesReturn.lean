import InitECandidate.Solver.Input.CurrentStartup.WitnessSlices
import InitECandidate.Solver.Input.CurrentStartup.WitnessLive
import InitECandidate.Solver.Input.CurrentStartup.ByteListCall
import InitECandidate.Solver.Input.CurrentStartup.CallerPairStores

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessNodesReturn
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord array : BitVec 64) (payloadLength start length : Nat) (value : ValueHOL 64) : Prop where
  startEq : start = 2 + Guest.GasLimit.le32 input 6 + 12
  lengthEq : length = Witness.offsetNat input (2 + Guest.GasLimit.le32 input 6) 1 - 12
  inside : start + length ≤ input.length % 2^64
  context : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength
  heap : NormalHeapEffects.AtLeast (max (record.toNat + 136) (requestRecord.toNat + 80)) current
  arrayAfter : max (record.toNat + 136) (requestRecord.toNat + 80) ≤ array.toNat
  heapExtent : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start length) current
  records : VarList.Records current input pointer array start length
  lengths : ∀ index < VarList.decodedCount input start length,
    (VarList.recordLength input start length (VarList.decodedCount input start length) index).toNat ≤ 1024
  nodePointer : current.memory (statelessRecord + 40#64) = .word (VarList.decodedArray array length)
  nodeCount : current.memory (statelessRecord + 48#64) = .word (BitVec.ofNat 64 (VarList.decodedCount input start length))
  locals : current.locals = source.locals.update (ofString "st0",
    BytesList.pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length))
  memory : ∀ query : BitVec 64, query.toNat < array.toNat →
    query ≠ statelessRecord + 40#64 → query ≠ statelessRecord + 48#64 → current.memory query = source.memory query
  price : source.clock - current.clock ≤ 2 * (length / 4) + 3
  clock : current.clock ≤ source.clock
  returned : evaluateHOLFiniteState current Witness.codeCall = (some (.returned value), post)
  origin : ∃ original originalPost, WitnessLoaded.Result (decoderOrigin := decoderOrigin) input original source originalPost
    pointer statelessRecord record gasWord requestRecord payloadLength value ∧ originalPost = restore source "st0" post

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ source current post, ∃ pointer statelessRecord record gasWord requestRecord array : BitVec 64,
    ∃ payloadLength start length : Nat, ∃ value : ValueHOL 64,
      Result (decoderOrigin := decoderOrigin) input source current post pointer statelessRecord record gasWord requestRecord array payloadLength start length value

/-- The first actual witness-list call and both actual output stores: physical
node records and1024-byte per-item bounds, with input/gas and bounded heap kept. -/
theorem loaded (input : Guest.InputBlob) (actual : WitnessLoaded.Reached (decoderOrigin := decoderOrigin) input) : Reached (decoderOrigin := decoderOrigin) input := by
  classical
  obtain ⟨original, source, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, value, data⟩ := actual
  let witnessStart := 2 + Guest.GasLimit.le32 input 6
  let start := witnessStart + 12
  let length := Witness.offsetNat input witnessStart 1 - 12
  obtain ⟨inside, args⟩ := WitnessSlices.node_arguments input original source post pointer statelessRecord record gasWord requestRecord payloadLength value data
  have normal := data.returned
  rw [Witness.arrays_shape.1] at normal
  let floor := max (record.toNat + 136) (requestRecord.toNat + 80)
  obtain ⟨decoded, inner, array, context, heap, heapExtent, locals, records, countLimit, lengths,
    memory, arrayLower, arrayAligned, arrayBound, forward, price, remaining, endpoint⟩ :=
    ByteListCall.normal input source post pointer statelessRecord record gasWord 9223372036854775807#64 1024#64
      payloadLength start length floor data.context (data.context.heap.maximum data.heap) (Nat.le_max_left _ _) inside
      "st0" _ Witness.afterNode (by decide) args value normal
  have countFacts := VarList.Records.cells decoded input pointer array start length context.domain records
  let count := BitVec.ofNat 64 (VarList.decodedCount input start length)
  have countNat : count.toNat = VarList.decodedCount input start length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := countFacts.2.1; omega)]
  have tuple : decoded.locals.lookup (ofString "st0") =
      some (VarList.pairValue (VarList.decodedArray array length) count.toNat) := by
    rw [locals, countNat]
    simp [HolFiniteMapExact.update, FUPDATE, BytesList.pairValue]
  have arena : WitnessRadix.AllocatedBytes.Arena statelessRecord 96 :=
    ⟨by have := context.pointerLower; have := context.statelessLower; omega, by have := context.statelessRoom; omega⟩
  obtain ⟨stores, firstCell, secondCell, frame⟩ := Witness.pair_stores decoded statelessRecord
    (VarList.decodedArray array length) count "st0" 40 Witness.codeCall context.si tuple context.domain arena
    context.statelessAligned (by decide) (by decide)
  let current := Witness.pairStored decoded statelessRecord 40 (VarList.decodedArray array length) count
  have currentContext := context.pair_stores input decoded pointer statelessRecord record gasWord
    (VarList.decodedArray array length) count payloadLength 40 "st0" (by decide) (by decide) tuple
  have currentRecords := Witness.records_after_pair_stores decoded input pointer array statelessRecord
    (VarList.decodedArray array length) count start length 40 records arena (by decide) (by
      have := context.recordAfter
      dsimp only [floor] at arrayLower
      omega)
  have run := remaining
  rw [Witness.arrays_shape.2.1, stores] at run
  exact ⟨source, current, inner, pointer, statelessRecord, record, gasWord, requestRecord, array,
    payloadLength, start, length, value,
    ⟨rfl, rfl, inside, currentContext, heap, arrayLower, heapExtent, currentRecords, lengths, firstCell, secondCell, locals,
      (fun query before firstAway secondAway => (frame query firstAway secondAway).trans (memory query before)),
      price, forward, run,
      ⟨original, post, data, endpoint⟩⟩⟩

/-- The real st0 binding and its two stores leave all witness slice locals live. -/
theorem Result.live {input : Guest.InputBlob} {source current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer statelessRecord record gasWord requestRecord array : BitVec 64} {payloadLength start length : Nat} {value : ValueHOL 64}
    (actual : Result (decoderOrigin := decoderOrigin) input source current post pointer statelessRecord record gasWord requestRecord array payloadLength start length value) :
    WitnessLive input current pointer := by
  obtain ⟨original, originalPost, data, endpoint⟩ := actual.origin
  have before : WitnessLive input source pointer := ⟨data.wp, data.wlen, data.w0, data.w1, data.w2⟩
  apply before.preserved
  intro name member
  rw [actual.locals]
  have different : ofString "st0" ≠ ofString name := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  simp [HolFiniteMapExact.update, FUPDATE, different]

theorem separated (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached (decoderOrigin := decoderOrigin) input :=
  loaded input (WitnessLoaded.separated input actual gas)

end InitECandidate.Solver.Input.CurrentStartup.WitnessNodesReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessNodesReturn.loaded
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessNodesReturn.separated

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessNodesReturn.Result.live
