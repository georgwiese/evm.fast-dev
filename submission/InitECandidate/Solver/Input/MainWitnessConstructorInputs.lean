import InitECandidate.Solver.Input.MainMptWorkspace
import InitECandidate.Solver.Input.MainHeaderValidatorContext
import InitECandidate.Solver.Input.RunAttemptConstructorsTrace
import InitECandidate.Solver.MutableTable.WitnessBuildDecodedInputs

namespace InitECandidate.Solver.Input.Main.WitnessConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def nodeStart (input : Guest.InputBlob) := DecoderCall.witnessStart input+Witness.offsetNat input (DecoderCall.witnessStart input) 0
def nodeBytes (input : Guest.InputBlob) := Witness.offsetNat input (DecoderCall.witnessStart input) 1-Witness.offsetNat input (DecoderCall.witnessStart input) 0
def codeStart (input : Guest.InputBlob) := DecoderCall.witnessStart input+Witness.offsetNat input (DecoderCall.witnessStart input) 1
def codeBytes (input : Guest.InputBlob) := Witness.offsetNat input (DecoderCall.witnessStart input) 2-Witness.offsetNat input (DecoderCall.witnessStart input) 1

def nodeCount (input : Guest.InputBlob) := VarList.decodedCount input (nodeStart input) (nodeBytes input)
def codeCount (input : Guest.InputBlob) := VarList.decodedCount input (codeStart input) (codeBytes input)
def nodeSlices (input : Guest.InputBlob) := MutableTable.WitnessBuild.decodedSlices input inputPointer (nodeStart input) (nodeBytes input)
def codeSlices (input : Guest.InputBlob) := MutableTable.WitnessBuild.decodedSlices input inputPointer (codeStart input) (codeBytes input)

/-- Main's actual header return retains the real witness decoder snapshot,
MPT/Keccak startup runtime and a heap frontier with room for both original
database constructors. Their counts share the same decoded witness bytes.
Only local/clock changes precede the real validator call. -/
theorem inputs_after_headers (input : Guest.InputBlob)
    (before copiedSource origin hashed callSource target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root headerRows : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase callSource=LocalEffects.erase hashed)
    (validated : Headers.Validate.Returned callSource target headerRows (PersistentAlloc.rounded root 32#64)
      (BitVec.ofNat 64 (HeaderSlices.count input)) 2713714688#64 2701135872#64 2713714976#64 2713715176#64
      (HeaderSlices.pointer input) (HeaderSlices.length input) inputPointer.toNat (PersistentAlloc.rounded root 32#64).toNat (input.length%2^64)) :
    ∃ codeArray headerArray heap,
      Witness.Inputs target input inputPointer (DecoderCall.witnessArray input) (RequestPrefix.cursor input) codeArray headerArray root
        (DecoderCall.witnessStart input) (Witness.offsetNat input (DecoderCall.witnessStart input) 0) (Witness.offsetNat input (DecoderCall.witnessStart input) 1)
        (Witness.offsetNat input (DecoderCall.witnessStart input) 2) (DecoderCall.witnessLength input) ∧
      MutableTable.WitnessBuild.Inputs target (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) heap (nodeCount input) 1024
        (nodeSlices input) 2713714976#64 2713715176#64 2713717584#64 ∧
      MutableTable.WitnessBuild.Inputs target (VarList.decodedArray codeArray (codeBytes input)) heap (codeCount input) 65536
        (codeSlices input) 2713714976#64 2713715176#64 2713717584#64 ∧
      heap.toNat+72+57*(4*nodeCount input+4)+7+72+57*(4*codeCount input+4)+7≤33806089496 ∧
      AllocatedBytes.Arena (RequestPrefix.cursor input) 96 ∧ (RequestPrefix.cursor input).toNat%8=0 ∧
      (RequestPrefix.cursor input).toNat+96≤heap.toNat ∧ inputPointer.toNat≤(RequestPrefix.cursor input).toNat := by
  have sourceMemory:=LocalEffects.memory_of_erase hashed callSource entryFrame
  have sourceDomain:=congrArg PanSemStateFiniteExact.memaddrs entryFrame
  have sourceEndian:=congrArg PanSemStateFiniteExact.be entryFrame
  have sourceCode:=congrArg PanSemStateFiniteExact.code entryFrame
  have sourceGlobals:=congrArg PanSemStateFiniteExact.globals entryFrame
  change callSource.memaddrs=hashed.memaddrs at sourceDomain
  change callSource.be=hashed.be at sourceEndian
  change callSource.code=hashed.code at sourceCode
  change callSource.globals=hashed.globals at sourceGlobals
  have frame : HashInput.Frame hashed target inputPointer.toNat (PersistentAlloc.rounded root 32#64).toNat :=
    ⟨by intro query low high; exact (validated.memory.words query low high).trans (congrFun sourceMemory query)⟩
  have transactions:=VarList.Records.count_input_bound origin input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  change Payload.transactionCount input≤(input.length%2^64)/4 at transactions
  obtain ⟨witnessNumber,witnessAligned,witnessAfter,witnessRoom,siArena,siAligned,siAfter,siBefore⟩ := DecoderCall.witness_geometry input bounded transactions
  obtain ⟨rootAligned,rootAfter,rootBound,rootArena⟩ := RequestRootHashData.frontier input (DecoderSetup.entered copiedSource input) origin root actual bounded prepared.originHeap
  have rootNumber : (PersistentAlloc.rounded root 32#64).toNat=root.toNat+32 := by
    rw [PersistentAlloc.rounded_nat root 32#64 (by have h:=rootArena.upper; change root.toNat+32+7<2^64; omega)]
    change (root.toNat+32+7)/8*8=root.toNat+32
    omega
  obtain ⟨codeArray,headerArray,inputs⟩ := witness_inputs_after_hash input (DecoderSetup.entered copiedSource input) origin hashed root counts actual bounded prepared returned
  have targetInputs:=inputs.of_frame hashed target input inputPointer (DecoderCall.witnessArray input) (RequestPrefix.cursor input) codeArray headerArray root
    (DecoderCall.witnessStart input) (Witness.offsetNat input (DecoderCall.witnessStart input) 0) (Witness.offsetNat input (DecoderCall.witnessStart input) 1)
    (Witness.offsetNat input (DecoderCall.witnessStart input) 2) (DecoderCall.witnessLength input) inputPointer.toNat (PersistentAlloc.rounded root 32#64).toNat
    frame (validated.domain.trans sourceDomain) (validated.endian.trans sourceEndian) (by decide)
    (by have h : input.length%2^64≤134217712 := bounded; change 2713731432+input.length%2^64<2^64; omega) (Nat.le_refl _)
    (by change 2713731432+input.length%2^64≤_; change 2713731432+input.length%2^64+8≤_ at witnessAfter; omega)
    (by change 2713731432≤_; change 2713731432+input.length%2^64+8≤_ at witnessAfter; omega) prepared.before siArena
    (by change 2713731432≤_; change 2713731432+input.length%2^64+8≤_ at siAfter; omega)
    (by omega)
  have finalCounts : root.toNat=(DecoderCall.witnessArray input).toNat+16*(nodeCount input+codeCount input+HeaderSlices.count input) := targetInputs.finalAddress
  have codeAddress : codeArray.toNat=(DecoderCall.witnessArray input).toNat+16*nodeCount input := targetInputs.codeAddress
  obtain ⟨heap,heapCell,heapBound,heapAligned,hashesBefore⟩ := validated.currentHeap
  have heapGrowth:=validated.heapBound heap heapCell
  have headerSmall:=validated.smallCount
  have heapCap : heap.toNat≤DecoderSetup.cursor input+168608+4*(input.length%2^64) := by rw [rootNumber] at heapGrowth; omega
  have rootBefore : root.toNat≤heap.toNat := by
    have before:=validated.geometry.hsBefore
    have first:=validated.geometry.hashesBefore
    rw [rootNumber] at before
    omega
  have witnessBytes : DecoderCall.witnessLength input≤input.length%2^64 := by unfold DecoderCall.witnessLength; omega
  have totalCounts : 4*(nodeCount input+codeCount input)≤input.length%2^64 := by
    have final:=targetInputs.finalAddress
    have finalBound:=targetInputs.finalBound
    change root.toNat=(DecoderCall.witnessArray input).toNat+16*(nodeCount input+codeCount input+_) at final
    omega
  have combinedRoom : heap.toNat+72+57*(4*nodeCount input+4)+7+72+57*(4*codeCount input+4)+7≤33806089496 := by
    have cursorBound:=(input_cursor_bounds input bounded).2.1
    change DecoderSetup.cursor input≤2847949152 at cursorBound
    have inputBound : input.length%2^64≤134217712 := bounded
    omega
  have scratchCell : target.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word 2713717584#64)) := by
    rw [validated.globals _ (by decide),sourceGlobals]
    exact MptWorkspace.after_hash_value input before copiedSource origin hashed root copied actual returned .hash
  have setup:=DecoderSetup.entered_context copiedSource input
  have setupEndian:=congrArg PanSemStateFiniteExact.be setup
  change (DecoderSetup.entered copiedSource input).be=copiedSource.be at setupEndian
  have little : target.be=false := validated.endian.trans (sourceEndian.trans (returned.endian.trans (actual.endian.trans (setupEndian.trans copied.little))))
  have installed : OriginalCode.Installed target.code := by rw [validated.code,sourceCode]; exact returned.workspace.sha.installed
  have arrayLower : inputPointer.toNat≤(DecoderCall.witnessArray input).toNat := by
    change 2713731432≤_
    change 2713731432+input.length%2^64+8≤_ at witnessAfter
    omega
  have codeLower : inputPointer.toNat≤codeArray.toNat := by have h:=targetInputs.codeAddress; omega
  have nodeBefore : (DecoderCall.witnessArray input).toNat+16*nodeCount input≤heap.toNat := by omega
  have codeBefore : codeArray.toNat+16*codeCount input≤heap.toNat := by omega
  have lowerHeap : 2701131776≤heap.toNat := by have h:=rootArena.lower; omega
  have nodes:=MutableTable.WitnessBuild.Inputs.of_decoded target input inputPointer (DecoderCall.witnessArray input) heap (nodeStart input) (nodeBytes input) 1024
    2713714976#64 2713715176#64 2713717584#64 targetInputs.nodes installed validated.environment scratchCell little heapCell lowerHeap heapAligned (by change heap.toNat+72+57*(4*nodeCount input+4)+7≤33806089496; omega) nodeBefore
    ⟨by decide,by decide⟩ (by decide) ⟨by decide,by decide⟩ (by decide) ⟨by decide,by decide⟩
    (by change 2713715176≤_ ∧ 2713715312≤_ ∧ 2713717616≤_; change 2713731432≤_ at arrayLower; omega) (by decide) targetInputs.nodeSizes
  have codes:=MutableTable.WitnessBuild.Inputs.of_decoded target input inputPointer codeArray heap (codeStart input) (codeBytes input) 65536
    2713714976#64 2713715176#64 2713717584#64 targetInputs.codes installed validated.environment scratchCell little heapCell lowerHeap heapAligned (by change heap.toNat+72+57*(4*codeCount input+4)+7≤33806089496; omega) codeBefore
    ⟨by decide,by decide⟩ (by decide) ⟨by decide,by decide⟩ (by decide) ⟨by decide,by decide⟩
    (by change 2713715176≤_ ∧ 2713715312≤_ ∧ 2713717616≤_; change 2713731432≤_ at codeLower; omega) (by decide) targetInputs.codeSizes
  exact ⟨codeArray,headerArray,heap,targetInputs,nodes,codes,combinedRoom,siArena,siAligned,by omega,by omega⟩

end InitECandidate.Solver.Input.Main.WitnessConstructors

#print axioms InitECandidate.Solver.Input.Main.WitnessConstructors.inputs_after_headers
