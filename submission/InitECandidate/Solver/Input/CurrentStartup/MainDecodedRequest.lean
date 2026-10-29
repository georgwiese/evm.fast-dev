import InitECandidate.Solver.Input.CurrentStartup.MainDecodedState
import InitECandidate.Solver.Input.CurrentStartup.DecodedRequestFields

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A concrete SI-field load uses the actual returned record's mapping and
cell, rather than treating physical memory contents as a successful load. -/
theorem WitnessHeadersReturn.Snapshot.si_load
    {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
    {post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer statelessRecord record gasWord requestRecord word : BitVec 64} {payloadLength : Nat}
    (snapshot : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input post
      pointer statelessRecord record gasWord requestRecord payloadLength)
    (si : post.locals.lookup (ofString "si") = some (.val (.word statelessRecord)))
    (offset : Nat) (inside : offset ≤ 88) (aligned : offset % 8 = 0)
    (cell : post.memory (statelessRecord + BitVec.ofNat 64 offset) = .word word) :
    eval post (.load .one (Scalar.plus (localVar "si") offset)) = some (.val (.word word)) := by
  obtain ⟨headerSource, ready, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    start, length, data, frame, clock⟩ := snapshot
  have readyFrame := frame.trans data.frame
  have domainFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) readyFrame
  have domain : post.memaddrs = InitE.ordinaryDomain := domainFrame.trans data.context.domain
  have arena : WitnessRadix.AllocatedBytes.Arena statelessRecord 96 :=
    ⟨by have := data.context.statelessLower; have := data.context.pointerLower; omega,
      by have := data.context.statelessRoom; omega⟩
  exact Witness.load_word_read post (Scalar.plus (localVar "si") offset) _ word
    (Scalar.plus_read post (localVar "si") statelessRecord offset (Request.local_word post "si" statelessRecord si))
    (WitnessRadix.AllocatedBytes.word_mapped post statelessRecord 96 offset domain arena (by omega)
      data.context.statelessAligned aligned) cell

/-- The actual root hasher's hash-list pointer/count, header and decoded
request pointer all load from the same original decoder snapshot. -/
theorem WitnessHeadersReturn.Snapshot.request_loads
    {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
    {post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer statelessRecord record gasWord requestRecord : BitVec 64} {payloadLength : Nat}
    (snapshot : WitnessHeadersReturn.Snapshot (decoderOrigin := decoderOrigin) input post
      pointer statelessRecord record gasWord requestRecord payloadLength)
    (si : post.locals.lookup (ofString "si") = some (.val (.word statelessRecord))) :
    eval post (.load .one (Scalar.plus (localVar "si") 8)) = some (.val (.word (pointer + 18#64 + Request.requestWords input 1))) ∧
    eval post (.load .one (Scalar.plus (localVar "si") 16)) = some (.val (.word (BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32)))) ∧
    eval post (.load .one (Scalar.plus (localVar "si") 24)) = some (.val (.word (pointer + 18#64 + 8#64))) ∧
    eval post (.load .one (Scalar.plus (localVar "si") 32)) = some (.val (.word requestRecord)) := by
  obtain ⟨hashPointer, hashCount, header, request⟩ := snapshot.request_fields
  exact ⟨snapshot.si_load si 8 (by decide) (by decide) hashPointer,
    snapshot.si_load si 16 (by decide) (by decide) hashCount,
    snapshot.si_load si 24 (by decide) (by decide) header,
    snapshot.si_load si 32 (by decide) (by decide) request⟩

/-- Main's genuine continuing decoder run supplies these physical hasher
arguments. Earlier stopped alternatives remain in MainDecodedState.cut. -/
theorem MainDecodedState.request_loads
    {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : HostState input source) (heap : NormalHeapEffects.AtLeast 2701135464 source)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)))
    (execution : CallPrefix.Execution source DecoderPrefix.actions target)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ pointer statelessRecord requestRecord : BitVec 64,
      target.locals.lookup (ofString "si") = some (.val (.word statelessRecord)) ∧
      eval target (.load .one (Scalar.plus (localVar "si") 8)) = some (.val (.word (pointer + 18#64 + Request.requestWords input 1))) ∧
      eval target (.load .one (Scalar.plus (localVar "si") 16)) = some (.val (.word (BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32)))) ∧
      eval target (.load .one (Scalar.plus (localVar "si") 24)) = some (.val (.word (pointer + 18#64 + 8#64))) ∧
      eval target (.load .one (Scalar.plus (localVar "si") 32)) = some (.val (.word requestRecord)) := by
  obtain ⟨origin, record, gasWord, requestRecord, payloadLength, run, si, snapshot⟩ :=
    MainDecodedState.current initial heap offsets execution gas
  exact ⟨origin.pointer, origin.word, requestRecord, si, snapshot.request_loads si⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.si_load
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.request_loads
#print axioms InitECandidate.Solver.Input.CurrentStartup.MainDecodedState.request_loads
