import InitECandidate.Solver.Input.MainRootHashProgram
import InitECandidate.Solver.Input.VarList.RecordsInputBound

namespace InitECandidate.Solver.Input.Main.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString

/-- The real decoder's final heap is aligned, after every decoded object and
has room for main's next32-byte root. Counts come from its actual record
arrays and share the copied-input budget, rather than an assumed heap model. -/
theorem parsed_heap (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : DecoderCall.DecoderReady input caller current) (bounded : input.length%2^64≤Guest.maxInputBytes) :
    ∃ heap : BitVec 64,current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      heap.toNat%8=0 ∧ (DecoderCall.witnessArray input).toNat≤heap.toNat ∧
      heap.toNat≤DecoderSetup.cursor input+600+8*(input.length%2^64) ∧ Arena heap 32 := by
  have transactions := VarList.Records.count_input_bound current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  change Payload.transactionCount input≤(input.length%2^64)/4 at transactions
  have geometry := DecoderCall.witness_geometry input bounded transactions
  obtain ⟨first,middleLower,ordered,lastUpper,codeArray,headerArray,heap,returned,nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,
    nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,heapWord,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩ := actual.decoded
  have witnessBound : DecoderCall.witnessLength input≤input.length%2^64 := by dsimp only [DecoderCall.witnessLength]; omega
  have bound : heap.toNat≤DecoderSetup.cursor input+600+8*(input.length%2^64) := by rw [geometry.1] at finalBound; omega
  have after : (DecoderCall.witnessArray input).toNat≤heap.toNat := by omega
  have inputAfter := geometry.2.2.1
  have upper : DecoderSetup.cursor input≤2847949152 := (input_cursor_bounds input bounded).2.1
  have small : input.length%2^64≤134217712 := bounded
  have arena : Arena heap 32 := ⟨by change 2713731432+input.length%2^64+8≤(DecoderCall.witnessArray input).toNat at inputAfter; omega,by omega⟩
  exact ⟨heap,heapWord,finalAligned,after,bound,arena⟩

end InitECandidate.Solver.Input.Main.RequestHash

#print axioms InitECandidate.Solver.Input.Main.RequestHash.parsed_heap
