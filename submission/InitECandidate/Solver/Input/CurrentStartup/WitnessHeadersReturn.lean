import InitECandidate.Solver.Input.CurrentStartup.WitnessCodesReturn

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (source ready post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord nodes codes headers : BitVec 64)
    (payloadLength nodeStart nodeLength codeStart codeLength start length : Nat) : Prop where
  startEq : start = 2 + Guest.GasLimit.le32 input 6 + Witness.offsetNat input (2 + Guest.GasLimit.le32 input 6) 2
  lengthEq : length = input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6 - Witness.offsetNat input (2 + Guest.GasLimit.le32 input 6) 2
  inside : start + length ≤ input.length % 2^64
  context : PayloadCallerReturn.Context input ready pointer statelessRecord record gasWord payloadLength
  frame : LocalEffects.erase post = LocalEffects.erase ready
  heap : NormalHeapEffects.AtLeast (max (record.toNat + 136) (requestRecord.toNat + 80)) post
  heapExtent : NormalHeapEffects.AtLeast (headers.toNat + 16 * VarList.decodedCount input start length) post
  nodeRecords : VarList.Records post input pointer nodes nodeStart nodeLength
  codeRecords : VarList.Records post input pointer codes codeStart codeLength
  headerRecords : VarList.Records post input pointer headers start length
  nodeLengths : ∀ index < VarList.decodedCount input nodeStart nodeLength,
    (VarList.recordLength input nodeStart nodeLength (VarList.decodedCount input nodeStart nodeLength) index).toNat ≤ 1024
  codeLengths : ∀ index < VarList.decodedCount input codeStart codeLength,
    (VarList.recordLength input codeStart codeLength (VarList.decodedCount input codeStart codeLength) index).toNat ≤ 65536
  headerLengths : ∀ index < VarList.decodedCount input start length,
    (VarList.recordLength input start length (VarList.decodedCount input start length) index).toNat ≤ 1024
  headerCountBound : VarList.decodedCount input start length ≤ 256
  headerPointer : post.memory (statelessRecord + 72#64) = .word (VarList.decodedArray headers length)
  headerCount : post.memory (statelessRecord + 80#64) = .word (BitVec.ofNat 64 (VarList.decodedCount input start length))
  image : Blob.HeapInput post input pointer
  gas : post.memory (record + 88#64) = .word gasWord
  price : source.clock - post.clock ≤ 2 * (length / 4) + 3
  clock : post.clock ≤ source.clock
  returned : evaluateHOLFiniteState source Witness.headerCall = (some (.returned (.val (.word statelessRecord))), post)
  origin : ∃ original, WitnessCodesReturn.Result (decoderOrigin := decoderOrigin) input original source post pointer statelessRecord record gasWord requestRecord nodes codes
    payloadLength nodeStart nodeLength codeStart codeLength (.val (.word statelessRecord))

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ source ready post, ∃ pointer statelessRecord record gasWord requestRecord nodes codes headers : BitVec 64,
    ∃ payloadLength nodeStart nodeLength codeStart codeLength start length : Nat,
      Result (decoderOrigin := decoderOrigin) input source ready post pointer statelessRecord record gasWord requestRecord nodes codes headers
        payloadLength nodeStart nodeLength codeStart codeLength start length

/-- The final witness list and both real output stores return the actual si
record. All three physical record arrays and their limits survive that return. -/
theorem codes (input : Guest.InputBlob) (actual : WitnessCodesReturn.Reached (decoderOrigin := decoderOrigin) input) : Reached (decoderOrigin := decoderOrigin) input := by
  classical
  obtain ⟨original, source, post, pointer, statelessRecord, record, gasWord, requestRecord, nodeArray, codeArray, payloadLength,
    nodeStart, nodeLength, codeStart, codeLength, value, data⟩ := actual
  let witnessStart := 2 + Guest.GasLimit.le32 input 6
  let first := Witness.offsetNat input witnessStart 2
  let total := input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6
  let start := witnessStart + first
  let length := total - first
  obtain ⟨nodeSource, nodePost, nodeData, nodeEndpoint⟩ := data.origin
  obtain ⟨oldSource, oldPost, initial, oldEndpoint⟩ := nodeData.origin
  have values := Witness.offset_values input witnessStart (BitVec.ofNat 64 total) initial.first initial.valid
  have totalNat : (BitVec.ofNat 64 total).toNat = total := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.mod_lt input.length (show 0 < 2^64 by decide); dsimp [total]; omega)]
  rw [totalNat] at values
  have outer := data.context.request.outer
  obtain ⟨inside, args⟩ := WitnessSlices.arguments_between input source pointer first total 256 1024 "w2" "wlen"
    (by have := outer.lower; have := outer.upper; omega) outer.upper values.2.2.2 (Nat.le_refl _)
    data.live.wp data.live.w2 data.live.wlen
  have normal := data.returned
  rw [Witness.arrays_shape.2.2.2.2.1] at normal
  let base := max (record.toNat + 136) (requestRecord.toNat + 80)
  let floor := max base (codeArray.toNat + 16 * VarList.decodedCount input codeStart codeLength)
  obtain ⟨decoded, inner, array, context, heap, heapExtent, locals, records, countLimit, lengths,
    memory, arrayLower, arrayAligned, arrayBound, forward, price, remaining, endpoint⟩ :=
    ByteListCall.normal input source post pointer statelessRecord record gasWord 256#64 1024#64
      payloadLength start length floor data.context (data.heap.maximum data.heapExtent) (by dsimp [floor, base]; omega) inside
      "hd" _ Witness.afterHeaders (by decide) args value normal
  have codesBefore : codeArray.toNat + 16 * VarList.decodedCount input codeStart codeLength ≤ array.toNat := by
    dsimp [floor] at arrayLower
    omega
  have nodesBefore : nodeArray.toNat + 16 * VarList.decodedCount input nodeStart nodeLength ≤ array.toNat := by
    have := data.nodesBefore
    omega
  have oldCodes := VarList.Records.of_before source decoded input pointer codeArray codeStart codeLength array.toNat
    data.codeRecords codesBefore memory
  have oldNodes := VarList.Records.of_before source decoded input pointer nodeArray nodeStart nodeLength array.toNat
    data.nodeRecords nodesBefore memory
  have countFacts := VarList.Records.cells decoded input pointer array start length context.domain records
  let count := BitVec.ofNat 64 (VarList.decodedCount input start length)
  have countNat : count.toNat = VarList.decodedCount input start length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := countFacts.2.1; omega)]
  have tuple : decoded.locals.lookup (ofString "hd") =
      some (VarList.pairValue (VarList.decodedArray array length) count.toNat) := by
    rw [locals, countNat]
    simp [HolFiniteMapExact.update, FUPDATE, BytesList.pairValue]
  have arena : WitnessRadix.AllocatedBytes.Arena statelessRecord 96 :=
    ⟨by have := context.pointerLower; have := context.statelessLower; omega, by have := context.statelessRoom; omega⟩
  obtain ⟨stores, firstCell, secondCell, storeFrame⟩ := Witness.pair_stores decoded statelessRecord
    (VarList.decodedArray array length) count "hd" 72 Witness.returnInput context.si tuple context.domain arena
    context.statelessAligned (by decide) (by decide)
  let ready := Witness.pairStored decoded statelessRecord 72 (VarList.decodedArray array length) count
  have readyContext := context.pair_stores input decoded pointer statelessRecord record gasWord
    (VarList.decodedArray array length) count payloadLength 72 "hd" (by decide) (by decide) tuple
  have siBefore : statelessRecord.toNat + 96 ≤ array.toNat := by
    have := context.recordAfter
    dsimp [floor, base] at arrayLower
    omega
  have readyHeaders := Witness.records_after_pair_stores decoded input pointer array statelessRecord
    (VarList.decodedArray array length) count start length 72 records arena (by decide) siBefore
  have readyCodes := Witness.records_after_pair_stores decoded input pointer codeArray statelessRecord
    (VarList.decodedArray array length) count codeStart codeLength 72 oldCodes arena (by decide) (by
      have := context.recordAfter
      have := data.arrayAfter
      omega)
  have readyNodes := Witness.records_after_pair_stores decoded input pointer nodeArray statelessRecord
    (VarList.decodedArray array length) count nodeStart nodeLength 72 oldNodes arena (by decide) (by
      have := context.recordAfter
      have := nodeData.arrayAfter
      omega)
  have run := remaining
  rw [Witness.arrays_shape.2.2.2.2.2, stores] at run
  have readySi : ready.locals.lookup (ofString "si") = some (.val (.word statelessRecord)) := readyContext.si
  have returned : evaluateHOLFiniteState ready Witness.returnInput =
      (some (.returned (.val (.word statelessRecord))), emptyLocalsHOLFinite ready) := by
    simp [Witness.returnInput, evaluateHOLFiniteState_return, evalHOLExact, toExact, localVar,
      readySi, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have same := returned.symm.trans run
  have valueEq : value = .val (.word statelessRecord) := by
    have result := congrArg Prod.fst same
    cases result
    rfl
  have innerEq : inner = emptyLocalsHOLFinite ready := (congrArg Prod.snd same).symm
  have postEq : post = restore source "hd" (emptyLocalsHOLFinite ready) := endpoint.trans (congrArg (restore source "hd") innerEq)
  have memoryEq : post.memory = ready.memory := by rw [postEq]; rfl
  have clockEq : post.clock = decoded.clock := by rw [postEq]; rfl
  have heapFinal : NormalHeapEffects.AtLeast base post := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := heap
    exact ⟨cursor, by rw [postEq]; exact cell, by dsimp [floor] at low; omega, high, aligned⟩
  have finalExtent : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start length) post := by
    rw [postEq]
    exact heapExtent
  refine ⟨source, ready, post, pointer, statelessRecord, record, gasWord, requestRecord, nodeArray, codeArray, array,
    payloadLength, nodeStart, nodeLength, codeStart, codeLength, start, length,
    ⟨rfl, rfl, inside, readyContext, ?_, heapFinal, finalExtent,
      VarList.Records.of_memory ready post input pointer nodeArray nodeStart nodeLength memoryEq readyNodes,
      VarList.Records.of_memory ready post input pointer codeArray codeStart codeLength memoryEq readyCodes,
      VarList.Records.of_memory ready post input pointer array start length memoryEq readyHeaders,
      data.nodeLengths, data.codeLengths, lengths, countLimit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [postEq]
    rfl
  · rw [memoryEq]
    exact firstCell
  · rw [memoryEq]
    exact secondCell
  · exact Blob.HeapInput.of_fields ready post input pointer memoryEq.symm (by rw [postEq]; rfl) (by rw [postEq]; rfl) readyContext.image
  · rw [memoryEq]
    exact readyContext.gasCell
  · rw [clockEq]
    exact price
  · rw [clockEq]
    exact forward
  · rw [← valueEq]
    exact data.returned
  · rw [← valueEq]
    exact ⟨original, data⟩

theorem separated (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached (decoderOrigin := decoderOrigin) input :=
  codes input (WitnessCodesReturn.separated input actual gas)

end InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.codes
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.separated
