import InitECandidate.Solver.Input.MainParsedByteBudget
import InitECandidate.Solver.Input.Requests.ByteBudget

namespace InitECandidate.Solver.Input.Main.RequestHash
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Sum of the actual parsed transaction payload lengths, excluding their
four-byte offset entries. Physical records in DecoderReady justify this sum. -/
def transactionDataBytes (input : Guest.InputBlob) : Nat :=
  VarList.sumPrefix (fun index=>(VarList.recordLength input (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input)
    (Payload.transactionCount input) index).toNat) (Payload.transactionCount input)

/-- All variable hashing data share one original input budget. The actual
five request record counts are tied to the physical ten-cell request image;
transaction offsets, fixed prefixes and witness data are charged once. -/
theorem parsed_hashing_byte_budget (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : DecoderCall.DecoderReady input caller current) :
    ∃ counts : Nat→BitVec 64,
      Requests.Layout (Requests.offsetWord input (DecoderCall.requestStart input)) (BitVec.ofNat 64 (DecoderCall.requestLength input)) ∧
      Requests.Image current (inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input)) (PayloadPrefix.finalCursor input)
        (BitVec.ofNat 64 (DecoderCall.requestLength input)) (Requests.offsetWord input (DecoderCall.requestStart input)) counts ∧
      622+(Guest.GasLimit.le32 input 566-540)+transactionDataBytes input+4*Payload.transactionCount input+
        44*Payload.withdrawalCount input+((PayloadPrefix.length input).toNat-Guest.GasLimit.le32 input 590)+
        32*((Guest.GasLimit.le32 input 58-Guest.GasLimit.le32 input 22)/32)+
        192*(counts 0).toNat+76*(counts 1).toNat+116*(counts 2).toNat+184*(counts 3).toNat+68*(counts 4).toNat+
        DecoderCall.witnessLength input≤input.length%2^64 := by
  obtain ⟨pointer,counts,requestLayout,requestImage⟩ := actual.requests
  have requestBudget := Requests.Image.byte_budget current (inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input))
    (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (DecoderCall.requestLength input)) (Requests.offsetWord input (DecoderCall.requestStart input)) counts requestImage requestLayout
  have ranges := actual.payloadLayout.ranges input (PayloadPrefix.length input)
  have lengthNumber : (PayloadPrefix.length input).toNat=Guest.GasLimit.le32 input 22-44 := by
    rw [PayloadPrefix.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have small := RawScalar.le32_lt input 22
    omega
  have requestLengthBound : DecoderCall.requestLength input<2^64 := by
    have small := RawScalar.le32_lt input 6
    dsimp only [DecoderCall.requestLength]
    omega
  have requestLengthNumber : (BitVec.ofNat 64 (DecoderCall.requestLength input)).toNat=DecoderCall.requestLength input := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt requestLengthBound]
  rw [requestLengthNumber] at requestBudget
  have transactionBudget := VarList.Records.byte_budget current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  change transactionDataBytes input+4*Payload.transactionCount input≤Payload.transactionBytes input at transactionBudget
  have withdrawalBudget := Nat.div_mul_le_self (Guest.GasLimit.le32 input 590-Guest.GasLimit.le32 input 570) 44
  have blobBudget := Nat.div_mul_le_self (Guest.GasLimit.le32 input 58-Guest.GasLimit.le32 input 22) 32
  have requestLower := actual.layout.requestLower
  have requestUpper := actual.layout.requestUpper
  have extent := actual.layout.extent
  have payloadLower := actual.layout.payloadLower
  have ordered := actual.layout.offsetsOrdered
  have upper := actual.layout.hashesUpper
  rw [lengthNumber] at ranges ⊢
  refine ⟨counts,requestLayout,requestImage,?_⟩
  dsimp only [DecoderCall.requestLength] at requestBudget
  dsimp only [Payload.transactionBytes] at transactionBudget
  dsimp only [Payload.withdrawalCount,DecoderCall.witnessLength]
  omega

end InitECandidate.Solver.Input.Main.RequestHash

#print axioms InitECandidate.Solver.Input.Main.RequestHash.parsed_hashing_byte_budget
