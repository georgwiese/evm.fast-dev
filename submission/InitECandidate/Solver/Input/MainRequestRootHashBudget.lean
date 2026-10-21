import InitECandidate.Solver.Input.MainRequestRootHashGeometry

namespace InitECandidate.Solver.Input.Main.RequestRootHashData
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Actual encoded bytes consumed by all original request-root hashing
inputs, including transaction offset entries and the fixed622-byte prefix. -/
def dataBytes (data : RequestRootHash.Description) :=
  622+data.payload.extraLength+VarList.sumPrefix data.payload.transactionLength data.payload.transactionCount+4*data.payload.transactionCount+
    44*data.payload.withdrawalCount+data.payload.balanceLength+32*data.blobCount+
    192*data.requestCount .deposit+76*data.requestCount .wdreq+116*data.requestCount .cons+184*data.requestCount .bdep+68*data.requestCount .bexit

/-- These exact hasher metadata/counts and physical request cells share the
same original input budget with the later witness decoder. -/
theorem budget (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : DecoderCall.DecoderReady input caller current) : ∃ counts : Nat→BitVec 64,
      Requests.Layout (Requests.offsetWord input (DecoderCall.requestStart input)) (BitVec.ofNat 64 (DecoderCall.requestLength input)) ∧
      Requests.Image current (inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input)) (PayloadPrefix.finalCursor input)
        (BitVec.ofNat 64 (DecoderCall.requestLength input)) (Requests.offsetWord input (DecoderCall.requestStart input)) counts ∧
      dataBytes (description input counts)+DecoderCall.witnessLength input≤input.length%2^64 := by
  obtain ⟨counts,requestLayout,requestImage,shared⟩ := RequestHash.parsed_hashing_byte_budget input caller current actual
  have balance := actual.payloadLayout.balance_length input (PayloadPrefix.length input)
  refine ⟨counts,requestLayout,requestImage,?_⟩
  dsimp only [dataBytes,description,PayloadHashData.description]
  rw [balance]
  exact shared

end InitECandidate.Solver.Input.Main.RequestRootHashData
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.budget
