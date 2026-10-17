import InitECandidate.Solver.MutableTable.WitnessPairedEnvironment
import InitECandidate.Solver.MutableTable.WitnessDecodedDictionaryCall
import InitECandidate.Solver.MutableTable.WitnessInputArgumentsAfterCall
import InitECandidate.Solver.MutableTable.WitnessAllocationBounds
import InitECandidate.Solver.Input.VarList.RecordsSafeFrame

namespace InitECandidate.Solver.MutableTable.WitnessRunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessBuild WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Derive the second actual decoded constructor call from the first call's
result. The second call, its heap cursor, preserved decoded cells and loaded
arguments are conclusions rather than independent constructor assumptions. -/
theorem paired_next_decoded_call (source right leftFirst rightFirst : PanSemStateFiniteExact 64 Guest.HostMemory)
    {nodeRecords nodeTable nodeCount : Nat}
    (nodeObservation : DictionaryObservation nodeRecords nodeTable nodeCount)
    (nodeSlices : BitVec 64 → Graph.Slice) (stp pad scratch si : BitVec 64)
    (maximumNode maximumCode boundary : Nat)
    (firstCall : ConstructorPairResult source right leftFirst rightFirst (arguments 40) (arguments 40)
      nodeObservation nodeSlices scratch maximumNode (fun query=>query.toNat<boundary)
      (fun query=>query.toNat<nodeTable ∧ Keccak256.Protected stp pad scratch query))
    (environment : PairedEnvironment source right stp pad scratch)
    (input : Guest.InputBlob) (pointer codeArray : BitVec 64) (codeStart codeLength : Nat)
    (decoded : Input.VarList.Records source input pointer codeArray codeStart codeLength)
    (arrayBefore : codeArray.toNat+16*Input.VarList.decodedCount input codeStart codeLength≤boundary)
    (boundaryBefore : boundary≤nodeTable)
    (room : nodeTable+72+57*(4*nodeCount+4)+7+72+57*(4*Input.VarList.decodedCount input codeStart codeLength+4)+7≤33806089496)
    (stateArena : Arena stp 200) (stateAligned : stp.toNat%8=0)
    (paddingArena : Arena pad 136) (paddingAligned : pad.toNat%8=0) (outputArena : Arena scratch 32)
    (buffersBeforeArray : stp.toNat+200≤codeArray.toNat ∧ pad.toNat+136≤codeArray.toNat ∧ scratch.toNat+32≤codeArray.toNat)
    (lengthBound : ∀ index<Input.VarList.decodedCount input codeStart codeLength,
      (Input.VarList.recordLength input codeStart codeLength (Input.VarList.decodedCount input codeStart codeLength) index).toNat≤maximumCode)
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (siArena : Arena si 96) (siAligned : si.toNat%8=0) (siBefore : si.toNat+96≤boundary)
    (buffersBeforeSI : stp.toNat+200≤si.toNat ∧ pad.toNat+136≤si.toNat ∧ scratch.toNat+32≤si.toNat)
    (pointerWord : source.memory (byteAddress si 56)=.word (BitVec.ofNat 64 (Input.VarList.decodedArray codeArray codeLength).toNat))
    (countWord : source.memory (byteAddress si 64)=.word (BitVec.ofNat 64 (Input.VarList.decodedCount input codeStart codeLength)))
    (locals : source.locals=right.locals) (endian : source.be=right.be)
    (leftClock : wholePrice maximumNode nodeCount+1+(wholePrice maximumCode (Input.VarList.decodedCount input codeStart codeLength)+2)≤source.clock)
    (rightClock : Constructor.wholePrice maximumNode nodeCount+1+(Constructor.wholePrice maximumCode (Input.VarList.decodedCount input codeStart codeLength)+2)≤right.clock) :
    ∃ logicalRecords,∃ observation : DictionaryObservation logicalRecords nodeObservation.heapEnd (Input.VarList.decodedCount input codeStart codeLength),
      ∃ leftSecond rightSecond,
        ConstructorPairResult (withTable leftFirst "nodedb" nodeTable) (withTable rightFirst "nodedb" nodeTable)
          leftSecond rightSecond (arguments 56) (arguments 56) observation (decodedSlice input pointer codeStart codeLength) scratch maximumCode
          (fun query=>query.toNat<boundary) (fun query=>query.toNat<nodeObservation.heapEnd ∧ Keccak256.Protected stp pad scratch query) ∧
        (Input.VarList.decodedCount input codeStart codeLength=0 → logicalRecords=nodeObservation.heapEnd) ∧
        (Input.VarList.decodedCount input codeStart codeLength≠0 → logicalRecords=(Input.VarList.decodedArray codeArray codeLength).toNat) := by
  classical
  let leftEntry:=withTable leftFirst "nodedb" nodeTable
  let rightEntry:=withTable rightFirst "nodedb" nodeTable
  have leftFields:=ConstructorReturn.fields source leftFirst (arguments 40) nodeTable firstCall.leftCall
  have rightFields:=ConstructorReturn.fields right rightFirst (arguments 40) nodeTable firstCall.rightCall
  have domains : right.memaddrs=source.memaddrs:=environment.rightEnvironment.domain.trans environment.entry.environment.domain.symm
  have argumentValues:=arguments_after_constructor source right leftFirst rightFirst (arguments 40) (arguments 40)
    nodeObservation nodeSlices stp pad scratch maximumNode boundary firstCall si siLocal locals environment.entry.environment.domain domains
    siArena siAligned siBefore boundaryBefore stateArena paddingArena outputArena buffersBeforeSI
    56 (Input.VarList.decodedArray codeArray codeLength).toNat (Input.VarList.decodedCount input codeStart codeLength)
    (by decide) (by decide) pointerWord countWord
  have preserved:=Input.VarList.Records.of_safe_frame source leftFirst input pointer codeArray codeStart codeLength nodeTable decoded
    (by omega) stp pad scratch stateArena paddingArena outputArena buffersBeforeArray firstCall.leftFrame
  have nextRecords:=Input.VarList.Records.of_memory leftFirst leftEntry input pointer codeArray codeStart codeLength rfl preserved
  have nextEntry:=EntryEnvironment.after_constructor source leftEntry nodeObservation.plan stp pad scratch firstCall.leftControl environment.entry
  have nextRight:=Keccak256.Environment.of_control (Constructor.preparedState right nodeObservation.plan) rightEntry stp pad firstCall.rightControl
    (Constructor.prepared_environment right nodeObservation.plan stp pad environment.rightEnvironment)
  have nextBounds:=ConstructorPairResult.heap_bounds source right leftFirst rightFirst (arguments 40) (arguments 40)
    nodeObservation nodeSlices scratch maximumNode _ _ firstCall
  have heapWords:=ConstructorPairResult.heap_words source right leftFirst rightFirst (arguments 40) (arguments 40)
    nodeObservation nodeSlices scratch maximumNode _ _ firstCall
  have tableBefore : nodeTable≤nodeObservation.heapEnd := by
    change nodeTable≤nodeTable+72+57*(2^nodeObservation.bits)+Constructor.padding (2^nodeObservation.bits)
    omega
  have nextLocals : leftEntry.locals=rightEntry.locals := by
    change leftFirst.locals.update _=rightFirst.locals.update _
    rw [firstCall.leftCall.locals,firstCall.rightCall.locals,locals]
  have nextEndian : leftEntry.be=rightEntry.be:=leftFields.2.1.trans (endian.trans rightFields.2.1.symm)
  have nextLeftClock : wholePrice maximumCode (Input.VarList.decodedCount input codeStart codeLength)+2≤leftEntry.clock := by
    change _≤leftFirst.clock
    have saved:=firstCall.leftLower
    omega
  have nextRightClock : Constructor.wholePrice maximumCode (Input.VarList.decodedCount input codeStart codeLength)+2≤rightEntry.clock := by
    change _≤rightFirst.clock
    have saved:=firstCall.rightLower
    omega
  apply paired_decoded_dictionary_call leftEntry rightEntry input pointer codeArray codeStart codeLength boundary nodeObservation.heapEnd maximumCode
    nextRecords (arguments 56) (arguments 56) argumentValues.1 argumentValues.2
    _ _ nextBounds.1 nextBounds.2.1 (by omega) heapWords.1 _ _ _ _ stp pad scratch nextEntry nextRight _ _
    stateArena stateAligned paddingArena paddingAligned outputArena buffersBeforeArray arrayBefore (by omega) lengthBound
    nextLocals firstCall.globals nextEndian firstCall.ffi firstCall.memory
    (fun query=>query.toNat<nodeObservation.heapEnd ∧ Keccak256.Protected stp pad scratch query)
    (by intro query safe;exact safe.1) (by intro query safe;exact safe.2) nextLeftClock nextRightClock
  · change leftFirst.code.lookup _=_
    rw [leftFields.2.2.2];exact environment.leftCode
  · change rightFirst.code.lookup _=_
    rw [rightFields.2.2.2];exact environment.rightCode
  · change leftFirst.code.lookup _=_
    rw [leftFields.2.2.2];exact environment.leftTableCode
  · change rightFirst.code.lookup _=_
    rw [rightFields.2.2.2];exact environment.rightTableCode
  · change leftFirst.code.lookup _=_
    rw [leftFields.2.2.2];exact environment.leftAllocCode
  · change rightFirst.code.lookup _=_
    rw [rightFields.2.2.2];exact environment.rightAllocCode
  · change rightFirst.code.lookup _=_
    rw [rightFields.2.2.2];exact environment.rightHashCode
  · change rightFirst.code.lookup _=_
    rw [rightFields.2.2.2];exact environment.helperCode

end InitECandidate.Solver.MutableTable.WitnessRunAttempt

#print axioms InitECandidate.Solver.MutableTable.WitnessRunAttempt.paired_next_decoded_call
