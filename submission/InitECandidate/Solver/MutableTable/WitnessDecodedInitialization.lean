import InitECandidate.Solver.MutableTable.WitnessNextDecodedCall

namespace InitECandidate.Solver.MutableTable.WitnessRunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessBuild WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Both real constructor invocations and both represented dictionaries at the
actual runtime entry follow from decoded input records and the initial fixed
metadata. No constructor run or second-entry heap is assumed. Frontend/header
reachability, the combined arena budget and whole-runtime proof remain separate. -/
theorem paired_decoded_initialization (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer nodeArray codeArray stp pad scratch si : BitVec 64)
    (nodeStart nodeLength codeStart codeLength nodeTable maximumNode maximumCode boundary : Nat)
    (environment : PairedEnvironment source right stp pad scratch)
    (nodes : Input.VarList.Records source input pointer nodeArray nodeStart nodeLength)
    (codes : Input.VarList.Records source input pointer codeArray codeStart codeLength)
    (nodeBefore : nodeArray.toNat+16*Input.VarList.decodedCount input nodeStart nodeLength≤boundary)
    (codeBefore : codeArray.toNat+16*Input.VarList.decodedCount input codeStart codeLength≤boundary)
    (boundaryBefore : boundary≤nodeTable)
    (tableLower : 2701131776≤nodeTable) (tableAligned : nodeTable%8=0)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 nodeTable))))
    (room : nodeTable+72+57*(4*Input.VarList.decodedCount input nodeStart nodeLength+4)+7+
      72+57*(4*Input.VarList.decodedCount input codeStart codeLength+4)+7≤33806089496)
    (stateArena : Arena stp 200) (stateAligned : stp.toNat%8=0)
    (paddingArena : Arena pad 136) (paddingAligned : pad.toNat%8=0) (outputArena : Arena scratch 32)
    (buffersBeforeNode : stp.toNat+200≤nodeArray.toNat ∧ pad.toNat+136≤nodeArray.toNat ∧ scratch.toNat+32≤nodeArray.toNat)
    (buffersBeforeCode : stp.toNat+200≤codeArray.toNat ∧ pad.toNat+136≤codeArray.toNat ∧ scratch.toNat+32≤codeArray.toNat)
    (nodeLengthBound : ∀ index<Input.VarList.decodedCount input nodeStart nodeLength,
      (Input.VarList.recordLength input nodeStart nodeLength (Input.VarList.decodedCount input nodeStart nodeLength) index).toNat≤maximumNode)
    (codeLengthBound : ∀ index<Input.VarList.decodedCount input codeStart codeLength,
      (Input.VarList.recordLength input codeStart codeLength (Input.VarList.decodedCount input codeStart codeLength) index).toNat≤maximumCode)
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (siArena : Arena si 96) (siAligned : si.toNat%8=0) (siBefore : si.toNat+96≤boundary)
    (buffersBeforeSI : stp.toNat+200≤si.toNat ∧ pad.toNat+136≤si.toNat ∧ scratch.toNat+32≤si.toNat)
    (nodePointerWord : source.memory (byteAddress si 40)=.word (BitVec.ofNat 64 (Input.VarList.decodedArray nodeArray nodeLength).toNat))
    (nodeCountWord : source.memory (byteAddress si 48)=.word (BitVec.ofNat 64 (Input.VarList.decodedCount input nodeStart nodeLength)))
    (codePointerWord : source.memory (byteAddress si 56)=.word (BitVec.ofNat 64 (Input.VarList.decodedArray codeArray codeLength).toNat))
    (codeCountWord : source.memory (byteAddress si 64)=.word (BitVec.ofNat 64 (Input.VarList.decodedCount input codeStart codeLength)))
    (locals : source.locals=right.locals) (globals : source.globals=right.globals) (endian : source.be=right.be) (ffi : source.ffi=right.ffi)
    (same : MemoryRegion.Agree (fun query=>query.toNat<boundary) source.memory right.memory)
    (leftClock : wholePrice maximumNode (Input.VarList.decodedCount input nodeStart nodeLength)+1+
      (wholePrice maximumCode (Input.VarList.decodedCount input codeStart codeLength)+2)≤source.clock)
    (rightClock : Constructor.wholePrice maximumNode (Input.VarList.decodedCount input nodeStart nodeLength)+1+
      (Constructor.wholePrice maximumCode (Input.VarList.decodedCount input codeStart codeLength)+2)≤right.clock) :
    ∃ nodeRecords,∃ nodeObservation : DictionaryObservation nodeRecords nodeTable (Input.VarList.decodedCount input nodeStart nodeLength),
      ∃ leftFirst rightFirst codeRecords,
        ∃ codeObservation : DictionaryObservation codeRecords nodeObservation.heapEnd (Input.VarList.decodedCount input codeStart codeLength),
          ∃ leftSecond rightSecond,
            let leftReady:=withTable leftSecond "codedb" nodeObservation.heapEnd
            let rightReady:=withTable rightSecond "codedb" nodeObservation.heapEnd
            DictionaryPair leftReady rightReady nodeObservation (decodedSlice input pointer nodeStart nodeLength) scratch ∧
              DictionaryPair leftReady rightReady codeObservation (decodedSlice input pointer codeStart codeLength) scratch ∧
              leftReady.locals=rightReady.locals ∧ leftReady.globals=rightReady.globals ∧ leftReady.ffi=rightReady.ffi ∧
              MemoryRegion.Agree (fun query=>query.toNat<boundary) leftReady.memory rightReady.memory ∧
              evaluateHOLFiniteState source initialization=
                (let output:=evaluateHOLFiniteState leftReady runtime;
                  (output.1,restore source "nodedb" (restore (withTable leftFirst "nodedb" nodeTable) "codedb" output.2))) ∧
              evaluateHOLFiniteState right initialization=
                (let output:=evaluateHOLFiniteState rightReady runtime;
                  (output.1,restore right "nodedb" (restore (withTable rightFirst "nodedb" nodeTable) "codedb" output.2))) := by
  classical
  have pointerGeometry:=input_field_geometry si stp pad scratch boundary nodeTable 40 siArena siBefore boundaryBefore
    stateArena paddingArena outputArena buffersBeforeSI (by decide)
  have countGeometry:=input_field_geometry si stp pad scratch boundary nodeTable 48 siArena siBefore boundaryBefore
    stateArena paddingArena outputArena buffersBeforeSI (by decide)
  have rightSi : right.locals.lookup (ofString "si")=some (.val (.word si)) := by rw [←locals];exact siLocal
  have domains : right.memaddrs=source.memaddrs:=environment.rightEnvironment.domain.trans environment.entry.environment.domain.symm
  have firstArguments:=paired_input_arguments source right si 40
    (Input.VarList.decodedArray nodeArray nodeLength).toNat (Input.VarList.decodedCount input nodeStart nodeLength)
    siLocal rightSi domains
    (word_mapped source si 96 40 environment.entry.environment.domain siArena (by decide) siAligned (by decide))
    (word_mapped source si 96 48 environment.entry.environment.domain siArena (by decide) siAligned (by decide))
    nodePointerWord nodeCountWord (fun query=>query.toNat<boundary) same pointerGeometry.1 countGeometry.1
  obtain ⟨nodeRecords,nodeObservation,leftFirst,rightFirst,firstCall,emptyBase,nonemptyBase⟩:=
    paired_decoded_dictionary_call source right input pointer nodeArray nodeStart nodeLength boundary nodeTable maximumNode nodes
      (arguments 40) (arguments 40) firstArguments.1 firstArguments.2 environment.leftCode environment.rightCode tableLower tableAligned
      (by omega) heap environment.leftTableCode environment.rightTableCode environment.leftAllocCode environment.rightAllocCode
      stp pad scratch environment.entry environment.rightEnvironment environment.rightHashCode environment.helperCode
      stateArena stateAligned paddingArena paddingAligned outputArena buffersBeforeNode nodeBefore boundaryBefore nodeLengthBound
      locals globals endian ffi same (fun query=>query.toNat<nodeTable ∧ Keccak256.Protected stp pad scratch query)
      (by intro query safe;exact safe.1) (by intro query safe;exact safe.2) (by omega) (by omega)
  obtain ⟨codeRecords,codeObservation,leftSecond,rightSecond,secondCall,codeEmptyBase,codeNonemptyBase⟩:=
    paired_next_decoded_call source right leftFirst rightFirst nodeObservation (decodedSlice input pointer nodeStart nodeLength)
      stp pad scratch si maximumNode maximumCode boundary firstCall environment input pointer codeArray codeStart codeLength codes
      codeBefore boundaryBefore room stateArena stateAligned paddingArena paddingAligned outputArena buffersBeforeCode codeLengthBound
      siLocal siArena siAligned siBefore buffersBeforeSI codePointerWord codeCountWord locals endian leftClock rightClock
  have buffersBeforeLogical : stp.toNat+200≤nodeRecords ∧ pad.toNat+136≤nodeRecords ∧ scratch.toNat+32≤nodeRecords := by
    by_cases empty : Input.VarList.decodedCount input nodeStart nodeLength=0
    · rw [emptyBase empty]
      exact ⟨by omega,by omega,by omega⟩
    · have lengthNonzero : nodeLength≠0 := by
        intro zero
        simp [Input.VarList.decodedCount,zero] at empty
      rw [nonemptyBase empty]
      simpa only [Input.VarList.decodedArray,if_neg lengthNonzero] using buffersBeforeNode
  refine ⟨nodeRecords,nodeObservation,leftFirst,rightFirst,codeRecords,codeObservation,leftSecond,rightSecond,?_⟩
  exact paired_initialization source right leftFirst rightFirst leftSecond rightSecond
    nodeRecords nodeTable (Input.VarList.decodedCount input nodeStart nodeLength)
    codeRecords nodeObservation.heapEnd (Input.VarList.decodedCount input codeStart codeLength) maximumNode maximumCode
    nodeObservation codeObservation (decodedSlice input pointer nodeStart nodeLength) (decodedSlice input pointer codeStart codeLength)
    stp pad scratch (fun query=>query.toNat<boundary) _ firstCall secondCall (by omega)
    stateArena paddingArena outputArena buffersBeforeLogical locals

end InitECandidate.Solver.MutableTable.WitnessRunAttempt

#print axioms InitECandidate.Solver.MutableTable.WitnessRunAttempt.paired_decoded_initialization
