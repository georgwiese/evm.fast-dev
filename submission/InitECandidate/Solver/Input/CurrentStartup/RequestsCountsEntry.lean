import InitECandidate.Solver.Input.CurrentStartup.RequestsAllocation
import InitECandidate.Solver.Input.Requests.OffsetLocals

namespace InitECandidate.Solver.Input.CurrentStartup.RequestsCountsEntry
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
  requestRoom : requestRecord.toNat + 80 ≤ 2952790016
  model : Requests.CountLocals current (Requests.offsetWord input start) (BitVec.ofNat 64 size)
    (pointer + BitVec.ofNat 64 start) requestRecord
  inside : start + size ≤ input.length % 2^64
  minimum : 20 ≤ size
  first : Requests.offsetWord input start 0 = 20#64
  valid : ∀ position < 5, Offsets.ValidAt 20#64 (BitVec.ofNat 64 size) (Requests.offsetWord input start) position
  gasCell : current.memory (record + 88#64) = .word gasWord
  returned : evaluateHOLFiniteState current Requests.countCalls = (some (.returned value), post)
  endpoint : ∃ entry originalPost, RequestsEntry.Result input caller entry originalPost pointer statelessRecord record gasWord payloadLength start size value ∧
    LocalEffects.erase originalPost = LocalEffects.erase post ∧ originalPost.clock = post.clock

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller current post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength start size : Nat, ∃ value : ValueHOL 64,
      Result input caller current post pointer statelessRecord record gasWord requestRecord payloadLength start size value

/-- Join the real already-allocated request to its five readonly declarations
and count calls. Original input, heap ownership and physical gas remain intact. -/
theorem allocated (input : Guest.InputBlob) (actual : RequestsAllocation.Reached input) : Reached input := by
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
  obtain ⟨entry, originalPost, original, originalFrame, originalClock⟩ := data.endpoint
  exact ⟨caller, current, innerPost, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, start, size, value,
    ⟨data.context, data.code, data.shapes, data.domain, data.endian,
      Blob.HeapInput.of_fields source current input pointer rfl rfl rfl data.image, data.heap, data.requestAfter,
      data.requestAligned, data.requestRoom, model, data.inside, data.minimum, data.first, data.valid, data.gasCell,
      Prod.ext resumed rfl, entry, originalPost, original, originalFrame.trans frame, originalClock.trans clock⟩⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  allocated input (RequestsAllocation.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.RequestsCountsEntry

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsCountsEntry.allocated
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsCountsEntry.separated
