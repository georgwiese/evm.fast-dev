import InitECandidate.Solver.Input.MainRequestRootHashTrace
import InitECandidate.Solver.Input.Witness.InputsFrame
import InitECandidate.Solver.Input.VarList.ConstructorData

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Main's actual normal root hashing retains all witness rows and SI
pointer/count cells at its constructor continuation. The original decoded
allocation frontier stays separate from the current post-root heap global. -/
theorem witness_inputs_after_hash (input : Guest.InputBlob) (caller origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (actual : DecoderCall.DecoderReady input caller origin) (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin current root) :
    ∃ codeArray headerArray,Witness.Inputs current input inputPointer (DecoderCall.witnessArray input) (RequestPrefix.cursor input) codeArray headerArray root
      (DecoderCall.witnessStart input) (Witness.offsetNat input (DecoderCall.witnessStart input) 0) (Witness.offsetNat input (DecoderCall.witnessStart input) 1)
      (Witness.offsetNat input (DecoderCall.witnessStart input) 2) (DecoderCall.witnessLength input) := by
  obtain ⟨first,middleLower,ordered,lastUpper,witness⟩ := actual.decoded
  obtain ⟨codeArray,headerArray,frontier,value,inputs,heap⟩ := Witness.inputs_of_decoded origin input inputPointer (DecoderCall.witnessArray input) (RequestPrefix.cursor input)
    (DecoderCall.witnessStart input) (Witness.offsetNat input (DecoderCall.witnessStart input) 0) (Witness.offsetNat input (DecoderCall.witnessStart input) 1)
    (Witness.offsetNat input (DecoderCall.witnessStart input) 2) (DecoderCall.witnessLength input) (.val (.word (RequestPrefix.cursor input))) witness
  have same : frontier=root := by
    have word := Option.some.inj (heap.symm.trans prepared.originHeap)
    cases word
    rfl
  subst frontier
  have transactions := VarList.Records.count_input_bound origin input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  change Payload.transactionCount input≤(input.length%2^64)/4 at transactions
  obtain ⟨witnessNumber,witnessAligned,witnessAfter,witnessRoom,siArena,siAligned,siAfter,siBefore⟩ := DecoderCall.witness_geometry input bounded transactions
  have frontierAfter : (DecoderCall.witnessArray input).toNat≤root.toNat := by have h:=inputs.finalAddress; omega
  have inputBound : input.length%2^64≤134217712 := bounded
  refine ⟨codeArray,headerArray,inputs.of_frame origin current input inputPointer (DecoderCall.witnessArray input) (RequestPrefix.cursor input) codeArray headerArray root
    (DecoderCall.witnessStart input) (Witness.offsetNat input (DecoderCall.witnessStart input) 0) (Witness.offsetNat input (DecoderCall.witnessStart input) 1)
    (Witness.offsetNat input (DecoderCall.witnessStart input) 2) (DecoderCall.witnessLength input) inputPointer.toNat root.toNat
    returned.input returned.domain returned.endian (by decide) (by change 2713731432+input.length%2^64<2^64; omega) (Nat.le_refl _)
    (by omega) (by omega) (Nat.le_refl _) siArena (by omega) (by omega)⟩

/-- All seventeen original payload fields survive hashing, including the
real gas/header fields later consumed by validation and EVM initialization. -/
theorem payload_image_after_hash (input : Guest.InputBlob) (caller origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (actual : DecoderCall.DecoderReady input caller origin) (prepared : RequestRootHashData.Prepared input origin root counts)
    (returned : RequestHash.Returned input origin current root) :
    Payload.Image current input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) :=
  returned.input.payload_image origin current input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    inputPointer.toNat root.toNat actual.image prepared.layout.payload.payloadArena prepared.layout.payload.payloadLower prepared.layout.payload.payloadBefore

/-- Real transaction decoder evidence survives the same hash call. The
zero-byte list keeps its empty branch without any readable-array premise. -/
theorem transaction_records_after_hash (input : Guest.InputBlob) (caller origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (actual : DecoderCall.DecoderReady input caller origin) (prepared : RequestRootHashData.Prepared input origin root counts)
    (returned : RequestHash.Returned input origin current root) :
    VarList.Records current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) := by
  by_cases empty : Payload.transactionBytes input=0
  · exact Or.inl empty
  · have positive : 0<Payload.transactionCount input := (VarList.Records.array_geometry origin input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
      (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records empty).1
    have lower := prepared.layout.payload.transactionLower positive
    have upper := prepared.layout.payload.transactionBefore positive
    change inputPointer.toNat≤(VarList.decodedArray (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (Payload.transactionBytes input)).toNat at lower
    change (VarList.decodedArray (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (Payload.transactionBytes input)).toNat+16*Payload.transactionCount input≤root.toNat at upper
    rw [VarList.decodedArray,if_neg empty] at lower upper
    exact returned.input.records origin current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
      (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) inputPointer.toNat root.toNat actual.records lower upper

end InitECandidate.Solver.Input.Main
#print axioms InitECandidate.Solver.Input.Main.witness_inputs_after_hash
#print axioms InitECandidate.Solver.Input.Main.payload_image_after_hash
#print axioms InitECandidate.Solver.Input.Main.transaction_records_after_hash
