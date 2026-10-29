import InitECandidate.Solver.Input.CurrentStartup.MainDecodedTransactions

namespace InitECandidate.Solver.Input.CurrentStartup.MainDecodedState
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete physical payload image belongs to the same actual decoder
run selected by main, including all hash fields and original transaction rows. -/
theorem payload_image {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : HostState input source) (heap : NormalHeapEffects.AtLeast 2701135464 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (execution : CallPrefix.Execution source DecoderPrefix.actions target)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ origin : DecoderOrigin, ∃ record gasWord requestRecord array : BitVec 64,
    ∃ payloadLength start size : Nat,
      MainSeparatedInput.RootRun input origin ∧
      target.locals.lookup (ofString "si") = some (.val (.word origin.word)) ∧
      WitnessHeadersReturn.Snapshot (decoderOrigin := origin) input target origin.pointer origin.word record gasWord requestRecord payloadLength ∧
      Payload.ReturnedImage input target origin.pointer record array payloadLength start size ∧
      array.toNat + 16 * VarList.decodedCount input start size ≤ requestRecord.toNat := by
  obtain ⟨origin, record, gasWord, requestRecord, payloadLength, run, si, snapshot⟩ :=
    current initial heap offsets execution gas
  obtain ⟨array, start, size, image, before⟩ := snapshot.payload_image
  exact ⟨origin, record, gasWord, requestRecord, array, payloadLength, start, size, run, si, snapshot, image, before⟩

end InitECandidate.Solver.Input.CurrentStartup.MainDecodedState

#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedState.payload_image
