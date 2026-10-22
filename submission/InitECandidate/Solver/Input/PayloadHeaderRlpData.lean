import InitECandidate.Solver.Input.PayloadHeaderPhysical
import InitECandidate.Solver.Input.RlpLength.EntryDeclarations
import InitECandidate.Solver.Input.HashInputDataFrame

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString Main WitnessRadix.QueryBranch

def lengthArray (input : Guest.InputBlob):=PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64
def lengthTxStart (input : Guest.InputBlob):=62+Guest.GasLimit.le32 input 566
def lengthWdStart (input : Guest.InputBlob):=62+Guest.GasLimit.le32 input 570

/-- Complete real block-length input evidence survives the original header
writes, including copied bytes, decoded transaction rows and all loop metadata. -/
theorem rlp_data (input : Guest.InputBlob) (before copiedSource origin source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root header : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (physical : PhysicalHeader input origin source current root header) :
    RlpLength.Block.Data current input inputPointer (lengthArray input) (PayloadPrefix.cursor input)
      (lengthTxStart input) (Payload.transactionBytes input) (lengthWdStart input) (Payload.withdrawalCount input) := by
  have bytes : Blob.HeapInput origin input inputPointer:=by
    obtain ⟨first,middleLower,ordered,lastUpper,codeArray,headerArray,heap,returned,nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,
      nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,heapWord,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩:=actual.decoded
    exact bytes
  have inputBound : input.length%2^64≤134217712:=bounded
  have cursorBounds:=input_cursor_bounds input bounded
  have payloadNumber:=(PayloadPrefix.cursor_number input bounded).1
  have payloadBefore : (PayloadPrefix.cursor input).toNat+136≤root.toNat:=prepared.layout.payload.payloadBefore
  have inputBefore : inputPointer.toNat+input.length%2^64≤root.toNat:=by
    have lower : 2713731432+input.length%2^64+8≤DecoderSetup.cursor input:=cursorBounds.1
    change 2713731432+input.length%2^64≤root.toNat
    rw [payloadNumber] at payloadBefore
    omega
  have callerDomain:=congrArg PanSemStateFiniteExact.memaddrs (DecoderSetup.entered_context copiedSource input)
  have callerEndian:=congrArg PanSemStateFiniteExact.be (DecoderSetup.entered_context copiedSource input)
  have originDomain : origin.memaddrs=InitE.ordinaryDomain:=actual.domain.trans (callerDomain.trans copied.domain)
  have originEndian : origin.be=false:=actual.endian.trans (callerEndian.trans copied.little)
  have heap:=physical.inputFrame.heap_input origin current input inputPointer _ _ bytes
    (physical.domain.trans originDomain.symm) (physical.little.trans originEndian.symm) (by decide)
    (by change 2713731432+input.length%2^64<2^64; omega) (Nat.le_refl _) inputBefore
  have arrayGeometry (nonempty : Payload.transactionBytes input≠0) :
      inputPointer.toNat≤(lengthArray input).toNat ∧
        (lengthArray input).toNat+16*Payload.transactionCount input≤root.toNat:=by
    have geometry:=actual.records.array_geometry origin input inputPointer (lengthArray input) (lengthTxStart input) (Payload.transactionBytes input) nonempty
    have positive : 0<(PayloadHashData.description input).transactionCount:=geometry.1
    have upper:=prepared.layout.payload.transactionBefore positive
    change (VarList.decodedArray (lengthArray input) (Payload.transactionBytes input)).toNat+16*Payload.transactionCount input≤root.toNat at upper
    simp only [VarList.decodedArray,if_neg nonempty] at upper
    exact ⟨by have lower:=geometry.2.2.2.2; omega,upper⟩
  have records : VarList.Records current input inputPointer (lengthArray input) (lengthTxStart input) (Payload.transactionBytes input):=by
    by_cases empty : Payload.transactionBytes input=0
    · exact Or.inl empty
    · obtain ⟨lower,upper⟩:=arrayGeometry empty
      exact physical.inputFrame.records origin current input inputPointer (lengthArray input) _ _ _ _ actual.records lower upper
  have image:=physical.inputFrame.payload_image origin current input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (lengthArray input) _ _
    actual.image prepared.layout.payload.payloadArena prepared.layout.payload.payloadLower prepared.layout.payload.payloadBefore
  have ranges:=actual.payloadLayout.ranges input (PayloadPrefix.length input)
  have lengthNumber : (PayloadPrefix.length input).toNat=Guest.GasLimit.le32 input 22-44:=by
    rw [PayloadPrefix.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have h:=RawScalar.le32_lt input 22
    omega
  have payloadInside : 62+(PayloadPrefix.length input).toNat≤input.length%2^64:=by
    have a:=actual.layout.extent
    have b:=actual.layout.payloadLower
    have c:=actual.layout.offsetsOrdered
    have d:=actual.layout.hashesUpper
    have e:=actual.layout.requestUpper
    rw [lengthNumber]
    omega
  have txBound : Payload.transactionBytes input≤134217712:=by
    dsimp [Payload.transactionBytes]
    omega
  have wdBound : Payload.withdrawalCount input<2^31:=by
    have bound : Payload.withdrawalCount input≤(input.length%2^64)/44:=prepared.layout.payload.withdrawalCountBound
    omega
  refine ⟨txBound,wdBound,heap,records,?_,?_,?_,?_,?_,?_⟩
  · change 62+Guest.GasLimit.le32 input 570+44*((Guest.GasLimit.le32 input 590-Guest.GasLimit.le32 input 570)/44)≤input.length%2^64
    omega
  · intro offset member
    have inside : offset<136 ∧ offset%8=0:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    exact AllocatedBytes.word_mapped current _ 136 offset physical.domain prepared.layout.payload.payloadArena inside.1
      prepared.layout.payload.payloadAligned inside.2
  · exact image (32,.rfield 0 (localVar "txs"),VarList.decodedArray (lengthArray input) (Payload.transactionBytes input))
      (by simp [Payload.imageFields,Payload.afterExtraFields])
  · exact image (40,.rfield 1 (localVar "txs"),BitVec.ofNat 64 (Payload.transactionCount input))
      (by simp [Payload.imageFields,Payload.afterExtraFields])
  · have cell:=image (48,.op .add [localVar "p",localVar "o_wd"],inputPointer+62#64+Payload.offsetWords input 2)
      (by simp [Payload.imageFields,Payload.afterExtraFields,Payload.remainingFields])
    simpa [lengthWdStart,Payload.offsetWords,BitVec.ofNat_add,BitVec.add_assoc] using cell
  · exact image (56,localVar "nwd",BitVec.ofNat 64 (Payload.withdrawalCount input))
      (by simp [Payload.imageFields,Payload.afterExtraFields,Payload.remainingFields])

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.rlp_data
