import InitECandidate.Solver.Input.CurrentStartup.RequestsAllocation
import InitECandidate.Solver.Input.Requests.OffsetLocals

namespace InitECandidate.Solver.Input.CurrentStartup.RequestsCountsEntry
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength start size : Nat) (value : ValueHOL 64) : Prop where
  context : PayloadCallerReturn.Context input caller pointer statelessRecord record gasWord payloadLength
  code : OriginalCode.Installed current.code
  shapes : OriginalExceptions.Installed current.eshapes
  domain : current.memaddrs = InitE.ordinaryDomain
  endian : current.be = false
  image : Blob.HeapInput current input pointer
  heap : NormalHeapEffects.AtLeast (requestRecord.toNat + 80) current
  requestAfter : record.toNat + 136 ≤ requestRecord.toNat
  requestAligned : requestRecord.toNat % 8 = 0
  callerHeap : caller.globals.lookup (ofString "heap_ptr") = some (.val (.word requestRecord))
  requestRoom : requestRecord.toNat + 80 ≤ 2952790016
  model : Requests.CountLocals current (Requests.offsetWord input start) (BitVec.ofNat 64 size)
    (pointer + BitVec.ofNat 64 start) requestRecord
  inside : start + size ≤ input.length % 2^64
  minimum : 20 ≤ size
  first : Requests.offsetWord input start 0 = 20#64
  valid : ∀ position < 5, Offsets.ValidAt 20#64 (BitVec.ofNat 64 size) (Requests.offsetWord input start) position
  gasCell : current.memory (record + 88#64) = .word gasWord
  returned : evaluateHOLFiniteState current Requests.countCalls = (some (.returned value), post)
  endpoint : ∃ entry originalPost, RequestsEntry.Result (decoderOrigin := decoderOrigin) input caller entry originalPost pointer statelessRecord record gasWord payloadLength start size value ∧
    WitnessRadix.BackingLayout.control current = WitnessRadix.BackingLayout.control (WitnessRadix.PersistentAlloc.post entry requestRecord 80#64) ∧
    current.clock ≤ entry.clock ∧ entry.clock - current.clock ≤ 13 ∧ LocalEffects.erase originalPost = LocalEffects.erase post ∧ originalPost.clock = post.clock ∧
    ∀ query : BitVec 64, query.toNat < 2701132528 ∨ 2701132528 + 40 ≤ query.toNat → current.memory query = entry.memory query

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller current post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength start size : Nat, ∃ value : ValueHOL 64,
      Result (decoderOrigin := decoderOrigin) input caller current post pointer statelessRecord record gasWord requestRecord payloadLength start size value

/-- Join the real already-allocated request to its five readonly declarations
and count calls. Original input, heap ownership and physical gas remain intact. -/
theorem allocated (input : Guest.InputBlob) (actual : RequestsAllocation.Reached (decoderOrigin := decoderOrigin) input) : Reached (decoderOrigin := decoderOrigin) input := by
  obtain ⟨caller, origin, source, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, start, size, value, data⟩ := actual
  obtain ⟨restoreStack, setup⟩ := Requests.offset_locals source input 2701132528#64 start data.workspace data.cells data.domain
    (by decide) ⟨by decide, by decide⟩
  let current := Requests.loadedOffsets source input start
  have model := Requests.loaded_offsets_model source input (pointer + BitVec.ofNat 64 start) requestRecord (BitVec.ofNat 64 size) start data.p data.len data.rq
  have declared := WitnessRadix.BuildEntry.declarations_execute setup Requests.countCalls
  have shape : WitnessRadix.BuildEntry.declarations Requests.offsetBindings Requests.countCalls = Requests.afterAllocation := by
    simpa only [Requests.offsetBindings, WitnessRadix.BuildEntry.declarations] using Requests.loads_shape.symm
  rw [shape] at declared
  have actual := declared.symm.trans data.returned
  have resumed : (evaluateHOLFiniteState current Requests.countCalls).1 = some (.returned value) := congrArg Prod.fst actual
  let innerPost := (evaluateHOLFiniteState current Requests.countCalls).2
  have postEq : post = restoreStack innerPost := (congrArg Prod.snd actual).symm
  have restoration := WitnessRadix.BuildEntry.restoration_frame setup innerPost
  have frame : LocalEffects.erase post = LocalEffects.erase innerPost := by
    rw [postEq]
    have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) restoration
    exact same
  have clock : post.clock = innerPost.clock := by
    rw [postEq]
    have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) restoration
    exact same
  obtain ⟨entry, originalPost, original, originControl, prefixForward, prefixCost, originalFrame, originalClock, prefixMemory⟩ := data.endpoint
  exact ⟨caller, current, innerPost, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, start, size, value,
    ⟨data.context, data.code, data.shapes, data.domain, data.endian,
      Blob.HeapInput.of_fields source current input pointer rfl rfl rfl data.image, data.heap, data.requestAfter,
      data.requestAligned, data.callerHeap, data.requestRoom, model, data.inside, data.minimum, data.first, data.valid, data.gasCell,
      Prod.ext resumed rfl, entry, originalPost, original, originControl, prefixForward, prefixCost, originalFrame.trans frame, originalClock.trans clock, prefixMemory⟩⟩

theorem separated (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached (decoderOrigin := decoderOrigin) input :=
  allocated input (RequestsAllocation.separated input actual gas)

end InitECandidate.Solver.Input.CurrentStartup.RequestsCountsEntry

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsCountsEntry.allocated
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsCountsEntry.separated
