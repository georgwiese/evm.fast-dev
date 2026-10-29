import InitECandidate.Solver.Input.CurrentStartup.MainDecodedState
import InitECandidate.Solver.Input.CurrentStartup.DecodedPayloadPointer

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both physical loads are justified by the actual decoder return and its
allocation/domain facts, including the nested payload gas load. -/
theorem WitnessHeadersReturn.Snapshot.payload_gas_load
    {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
    {post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer statelessRecord record gasWord requestRecord : BitVec 64} {payloadLength : Nat}
    (snapshot : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input post
      pointer statelessRecord record gasWord requestRecord payloadLength)
    (si : post.locals.lookup (ofString "si") = some (.val (.word statelessRecord))) :
    eval post (.load .one (Scalar.plus (localVar "si") 0)) = some (.val (.word record)) ∧
    eval post (.load .one (Scalar.plus (.load .one (Scalar.plus (localVar "si") 0)) 88)) = some (.val (.word gasWord)) ∧
    gasWord.toNat ≤ 200000000 := by
  have pointerCell := snapshot.payload_cell
  obtain ⟨headerSource, ready, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    start, length, data, frame, clock⟩ := snapshot
  have readyFrame := frame.trans data.frame
  have domainFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) readyFrame
  have domain : post.memaddrs = InitE.ordinaryDomain := domainFrame.trans data.context.domain
  have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) frame
  change post.memory = headerPost.memory at memory
  have siArena : WitnessRadix.AllocatedBytes.Arena statelessRecord 96 :=
    ⟨by have := data.context.statelessLower; have := data.context.pointerLower; omega,
      by have := data.context.statelessRoom; omega⟩
  have payloadArena : WitnessRadix.AllocatedBytes.Arena record 136 :=
    ⟨by have := data.context.statelessLower; have := data.context.pointerLower; have := data.context.recordAfter; omega,
      by have := data.context.recordRoom; omega⟩
  have siMapped := WitnessRadix.AllocatedBytes.word_mapped post statelessRecord 96 0 domain siArena
    (by decide) data.context.statelessAligned (by decide)
  have gasMapped := WitnessRadix.AllocatedBytes.word_mapped post record 136 88 domain payloadArena
    (by decide) data.context.recordAligned (by decide)
  have pointerRead := Witness.load_word_read post (Scalar.plus (localVar "si") 0) statelessRecord record
    (by simpa using Scalar.plus_read post (localVar "si") statelessRecord 0 (Request.local_word post "si" statelessRecord si))
    (by simpa [WitnessRadix.byteAddress] using siMapped) pointerCell
  have gasCell : post.memory (record + 88#64) = .word gasWord := by rw [memory]; exact data.gas
  have gasRead := Witness.load_word_read post (Scalar.plus (.load .one (Scalar.plus (localVar "si") 0)) 88)
    (record + 88#64) gasWord
    (Scalar.plus_read post (.load .one (Scalar.plus (localVar "si") 0)) record 88 pointerRead)
    gasMapped gasCell
  exact ⟨pointerRead, gasRead, data.context.gasBound⟩

/-- Main's actual continuing decoder return supplies its real payload-pointer
load and bounded gas load. No other decoder execution is substituted. -/
theorem MainDecodedState.payload_gas_load
    {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : HostState input source) (heap : NormalHeapEffects.AtLeast 2701135464 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (execution : CallPrefix.Execution source DecoderPrefix.actions target)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ statelessRecord record gasWord : BitVec 64,
      target.locals.lookup (ofString "si") = some (.val (.word statelessRecord)) ∧
      target.memory statelessRecord = .word record ∧
      eval target (.load .one (Scalar.plus (localVar "si") 0)) = some (.val (.word record)) ∧
      eval target (.load .one (Scalar.plus (.load .one (Scalar.plus (localVar "si") 0)) 88)) = some (.val (.word gasWord)) ∧
      gasWord.toNat ≤ 200000000 := by
  obtain ⟨origin, record, gasWord, requestRecord, payloadLength, run, si, snapshot⟩ :=
    MainDecodedState.current initial heap offsets execution gas
  exact ⟨origin.word, record, gasWord, si, snapshot.payload_cell, snapshot.payload_gas_load si⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.payload_gas_load
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedState.payload_gas_load
