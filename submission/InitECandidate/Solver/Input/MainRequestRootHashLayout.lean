import InitECandidate.Solver.Input.MainRequestRootHashInputs

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.Main.RequestRootHashData
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- All metadata and input extents required by the whole original request
root hash come from this same decoded main state and its prehash frontier. -/
theorem layout (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat→BitVec 64) (root : BitVec 64)
    (actual : DecoderCall.DecoderReady input caller current) (bounded : input.length%2^64≤Guest.maxInputBytes)
    (after : (DecoderCall.witnessArray input).toNat≤root.toNat)
    (requestLayout : Requests.Layout (Requests.offsetWord input (DecoderCall.requestStart input)) (BitVec.ofNat 64 (DecoderCall.requestLength input)))
    (requestImage : Requests.Image current (inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input)) (PayloadPrefix.finalCursor input)
      (BitVec.ofNat 64 (DecoderCall.requestLength input)) (Requests.offsetWord input (DecoderCall.requestStart input)) counts) :
    (description input counts).Layout inputPointer.toNat root.toNat (input.length%2^64) := by
  have inputBound : input.length%2^64≤134217712 := bounded
  have inputNumber : inputPointer.toNat=2713731432 := rfl
  have decodedLower : inputPointer.toNat+input.length%2^64+8≤DecoderSetup.cursor input := (input_cursor_bounds input bounded).1
  have transactions := VarList.Records.count_input_bound current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  change Payload.transactionCount input≤(input.length%2^64)/4 at transactions
  obtain ⟨witnessNumber,witnessAligned,witnessAfter,witnessRoom,siArena,siAligned,siAfter,siBefore⟩ := DecoderCall.witness_geometry input bounded transactions
  obtain ⟨requestNumber,requestAligned,requestLower,requestUpper⟩ := PayloadPrefix.final_cursor_geometry input bounded transactions
  have inputs := request_inputs input caller current counts actual bounded requestLayout requestImage
  have inputArena : AllocatedBytes.Arena inputPointer (input.length%2^64) := ⟨by decide,by change 2713731432+input.length%2^64≤33806089496; omega⟩
  have hashesUpper := actual.layout.hashesUpper
  have hashesLower := actual.layout.offsetsOrdered
  have requestContained := actual.layout.requestUpper
  have extent := actual.layout.extent
  have blobPointer : (description input counts).blobs=inputPointer+BitVec.ofNat 64 (18+Guest.GasLimit.le32 input 22) := by
    change inputPointer+18#64+BitVec.ofNat 64 (Guest.GasLimit.le32 input 22)=_
    rw [BitVec.ofNat_add,←BitVec.add_assoc]
  refine {
    payload := PayloadHashData.layout input caller current root actual bounded after
    siArena := AllocatedBytes.Arena.weaken _ 96 40 siArena (by decide)
    siAligned := siAligned
    siLower := by change inputPointer.toNat≤(RequestPrefix.cursor input).toNat; omega
    siBefore := by change (RequestPrefix.cursor input).toNat+40≤root.toNat; omega
    blobsBound := ?_
    blobsArena := ?_
    parentArena := AllocatedBytes.Arena.subrange inputPointer (input.length%2^64) 26 32 inputArena (by omega)
    requestsArena := ?_
    requestsAligned := requestAligned
    requestsLower := by change inputPointer.toNat≤(PayloadPrefix.finalCursor input).toNat; omega
    requestsBefore := by change (PayloadPrefix.finalCursor input).toNat+80≤root.toNat; omega
    requestCounts := fun kind=>(inputs kind).1
    requestInputs := fun kind=>(inputs kind).2
  }
  · change (Guest.GasLimit.le32 input 58-Guest.GasLimit.le32 input 22)/32≤(input.length%2^64)/32
    omega
  · rw [blobPointer]
    exact AllocatedBytes.Arena.subrange inputPointer (input.length%2^64) (18+Guest.GasLimit.le32 input 22)
      (32*((Guest.GasLimit.le32 input 58-Guest.GasLimit.le32 input 22)/32)) inputArena (by omega)
  · change AllocatedBytes.Arena (PayloadPrefix.finalCursor input) 80
    exact ⟨by omega,by omega⟩

end InitECandidate.Solver.Input.Main.RequestRootHashData
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.layout
