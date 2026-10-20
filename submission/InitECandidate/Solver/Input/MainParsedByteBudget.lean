import InitECandidate.Solver.Input.MainParsedHeap
import InitECandidate.Solver.Input.VarList.RecordByteBudget

namespace InitECandidate.Solver.Input.Main.RequestHash
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Payload transaction bytes and witness bytes are disjoint portions of the
same actual input. This avoids paying a separate maximum for each array. -/
theorem parsed_byte_budget (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : DecoderCall.DecoderReady input caller current) :
    Payload.transactionBytes input+DecoderCall.witnessLength input≤input.length%2^64 ∧
      16*Payload.transactionCount input+4*DecoderCall.witnessLength input≤4*(input.length%2^64) := by
  have ranges := actual.payloadLayout.ranges input (PayloadPrefix.length input)
  have lengthNumber : (PayloadPrefix.length input).toNat=Guest.GasLimit.le32 input 22-44 := by
    rw [PayloadPrefix.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have small := RawScalar.le32_lt input 22
    omega
  rw [lengthNumber] at ranges
  have lower := actual.layout.requestLower
  have upper := actual.layout.requestUpper
  have extent := actual.layout.extent
  have ordered := actual.layout.offsetsOrdered
  have contained := actual.layout.hashesUpper
  have payloadLower := actual.layout.payloadLower
  have shared : Payload.transactionBytes input+DecoderCall.witnessLength input≤input.length%2^64 := by
    dsimp only [Payload.transactionBytes,DecoderCall.witnessLength]
    omega
  have records := VarList.Records.byte_budget current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  change _+4*Payload.transactionCount input≤Payload.transactionBytes input at records
  exact ⟨shared,by omega⟩

/-- The reached original heap uses one shared input budget across transaction
and witness records, rather than two independent maximum input lengths. -/
theorem parsed_heap_shared (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : DecoderCall.DecoderReady input caller current) (bounded : input.length%2^64≤Guest.maxInputBytes) :
    ∃ heap : BitVec 64,current.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr")=some (.val (.word heap)) ∧
      heap.toNat%8=0 ∧ (DecoderCall.witnessArray input).toNat≤heap.toNat ∧
      heap.toNat≤DecoderSetup.cursor input+600+4*(input.length%2^64) ∧ WitnessRadix.AllocatedBytes.Arena heap 32 := by
  have transactions := VarList.Records.count_input_bound current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  change Payload.transactionCount input≤(input.length%2^64)/4 at transactions
  have geometry := DecoderCall.witness_geometry input bounded transactions
  have shared := (parsed_byte_budget input caller current actual).2
  obtain ⟨first,middleLower,ordered,lastUpper,codeArray,headerArray,heap,returned,nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,
    nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,heapWord,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩ := actual.decoded
  have bound : heap.toNat≤DecoderSetup.cursor input+600+4*(input.length%2^64) := by rw [geometry.1] at finalBound; omega
  have after : (DecoderCall.witnessArray input).toNat≤heap.toNat := by omega
  have inputAfter := geometry.2.2.1
  have upper : DecoderSetup.cursor input≤2847949152 := (input_cursor_bounds input bounded).2.1
  have small : input.length%2^64≤134217712 := bounded
  exact ⟨heap,heapWord,finalAligned,after,bound,⟨by change 2713731432+input.length%2^64+8≤(DecoderCall.witnessArray input).toNat at inputAfter; omega,by omega⟩⟩

end InitECandidate.Solver.Input.Main.RequestHash

#print axioms InitECandidate.Solver.Input.Main.RequestHash.parsed_byte_budget
#print axioms InitECandidate.Solver.Input.Main.RequestHash.parsed_heap_shared
