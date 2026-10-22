import InitECandidate.Solver.Input.PayloadHeaderRlpData

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack PanSemStateFiniteExact WitnessRadix
open Main

/-- All source input/record cells read by block_rlp_length precede its
true temporary buffer. Empty transaction arrays require no owned span. -/
theorem length_regions (input : Guest.InputBlob) (caller origin source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root header : BitVec 64) (counts : Nat→BitVec 64)
    (actual : DecoderCall.DecoderReady input caller origin) (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (physical : PhysicalHeader input origin source current root header) :
    inputPointer.toNat+input.length%2^64≤(headerFrontier header).toNat ∧
      (Payload.transactionBytes input≠0→(lengthArray input).toNat+16*Payload.transactionCount input≤(headerFrontier header).toNat) ∧
      (∀ offset∈([32,40,48,56] : List Nat),(PayloadPrefix.cursor input+BitVec.ofNat 64 offset).toNat<(headerFrontier header).toNat) := by
  have rootBefore:=physical.rootBefore
  have headerBefore:=physical.frontier.afterHeader
  have payloadBefore : (PayloadPrefix.cursor input).toNat+136≤root.toNat:=prepared.layout.payload.payloadBefore
  have payloadNumber:=(PayloadPrefix.cursor_number input bounded).1
  have inputLower : 2713731432+input.length%2^64+8≤DecoderSetup.cursor input:=(input_cursor_bounds input bounded).1
  constructor
  · change 2713731432+input.length%2^64≤_
    rw [payloadNumber] at payloadBefore
    omega
  constructor
  · intro nonempty
    have geometry:=actual.records.array_geometry origin input inputPointer (lengthArray input) (lengthTxStart input) (Payload.transactionBytes input) nonempty
    have positive : 0<(PayloadHashData.description input).transactionCount:=geometry.1
    have upper:=prepared.layout.payload.transactionBefore positive
    change (VarList.decodedArray (lengthArray input) (Payload.transactionBytes input)).toNat+16*Payload.transactionCount input≤root.toNat at upper
    simp only [VarList.decodedArray,if_neg nonempty] at upper
    omega
  · intro offset member
    have inside : offset<136:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    have number:=byteAddress_toNat (PayloadPrefix.cursor input) offset (by have h:=prepared.layout.payload.payloadArena.upper; omega)
    change (PayloadPrefix.cursor input+BitVec.ofNat 64 offset).toNat=(PayloadPrefix.cursor input).toNat+offset at number
    omega

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.length_regions
