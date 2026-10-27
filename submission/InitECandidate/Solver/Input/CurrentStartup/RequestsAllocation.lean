import InitECandidate.Solver.Input.CurrentStartup.RequestsValidated
import InitECandidate.Solver.Input.Requests.LayoutProgram

namespace InitECandidate.Solver.Input.CurrentStartup.RequestsAllocation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (caller source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
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
  sourceHeap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word requestRecord))
  exactState : current = setVarHOLFinite (ofString "rq") (.val (.word requestRecord))
    (WitnessRadix.PersistentAlloc.post {source with clock := source.clock - 1} requestRecord 80#64)
  rq : current.locals.lookup (ofString "rq") = some (.val (.word requestRecord))
  p : current.locals.lookup (ofString "p") = some (.val (.word (pointer + BitVec.ofNat 64 start)))
  len : current.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 size)))
  workspace : current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64))
  inside : start + size ≤ input.length % 2^64
  minimum : 20 ≤ size
  first : Requests.offsetWord input start 0 = 20#64
  valid : ∀ position < 5, Offsets.ValidAt 20#64 (BitVec.ofNat 64 size) (Requests.offsetWord input start) position
  cells : ∀ position < 5, current.memory (WitnessRadix.byteAddress 2701132528#64 (8 * position)) = .word (Requests.offsetWord input start position)
  gasCell : current.memory (record + 88#64) = .word gasWord
  returned : evaluateHOLFiniteState current Requests.afterAllocation = (some (.returned value), post)
  endpoint : ∃ entry originalPost, RequestsEntry.Result input caller entry originalPost pointer statelessRecord record gasWord payloadLength start size value ∧
    LocalEffects.erase originalPost = LocalEffects.erase post ∧ originalPost.clock = post.clock

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller source current post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength start size : Nat, ∃ value : ValueHOL 64,
      Result input caller source current post pointer statelessRecord record gasWord requestRecord payloadLength start size value

/-- The real normal request allocation derives its actual80-byte room and
exact heap update. Ordinary backing geometry is not an allocation-room premise. -/
theorem validated (input : Guest.InputBlob) (actual : RequestsValidated.Reached input) : Reached input := by
  obtain ⟨caller, source, post, pointer, statelessRecord, record, gasWord, payloadLength, start, size, value, data⟩ := actual
  let actions : List CallPrefix.Action := [.scoped (ofString "rq") .one (Code.name .alloc) [.const 80#64]]
  have shape : Requests.afterOffsets = CallPrefix.program actions Requests.afterAllocation := by
    simpa only [actions, CallPrefix.program, Code.name] using Requests.allocation_shape
  have never : NoReturn.Never (CallPrefix.program actions .skip) := @CallPrefix.kept_never actions (ofString "unused") (by
    intro action member
    simp only [actions, List.mem_singleton] at member
    subst action
    decide)
  have run := data.returned
  rw [shape] at run
  obtain ⟨current, innerPost, execution, remaining, clock, frame⟩ :=
    CallPrefix.normal_frame_trace source post actions Requests.afterAllocation value never run
  have allocated : CallPrefix.Reaches source (.scoped (ofString "rq") .one (Code.name .alloc) [.const 80#64]) current := by
    change CallPrefix.Execution source [.scoped (ofString "rq") .one (Code.name .alloc) [.const 80#64]] current at execution
    cases execution with
    | step first rest => cases rest; exact first
  obtain ⟨requestRecord, sourceHeap, afterRecord, aligned, room, stateEq, heap⟩ :=
    allocation_frontier_after (ofString "rq") 80#64 (record.toNat + 136) data.code data.heap allocated
  have image : Blob.HeapInput current input pointer := Blob.HeapInput.of_fields source current input pointer
    (by rw [stateEq]; rfl) (by rw [stateEq]; rfl) (by rw [stateEq]; rfl) data.image
  have code : OriginalCode.Installed current.code := by rw [stateEq]; exact data.code
  have shapes : OriginalExceptions.Installed current.eshapes := by rw [stateEq]; exact data.shapes
  have domain : current.memaddrs = InitE.ordinaryDomain := by rw [stateEq]; exact data.domain
  have endian : current.be = false := by rw [stateEq]; exact data.endian
  have workspace : current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) := by
    rw [stateEq]
    simpa [setVarHOLFinite, WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "ssz_offs" from by decide] using data.workspace
  have kept (name : String) (other : ofString "rq" ≠ ofString name) :
      current.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    rw [stateEq]
    simp [setVarHOLFinite, WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE, other]
  obtain ⟨entry, originalPost, original, originalFrame, originalClock⟩ := data.endpoint
  refine ⟨caller, source, current, innerPost, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, start, size, value,
    ⟨data.context, code, shapes, domain, endian, image, heap, afterRecord, aligned, room, sourceHeap, stateEq, ?_,
      (kept "p" (by decide)).trans data.p, (kept "len" (by decide)).trans data.len, workspace, data.inside, data.minimum,
      data.first, data.valid, ?_, ?_, remaining, entry, originalPost, original, originalFrame.trans frame, originalClock.trans clock⟩⟩
  · rw [stateEq]
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · intro position inside
    rw [stateEq]
    exact data.cells position inside
  · rw [stateEq]
    exact data.gasCell

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  validated input (RequestsValidated.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.RequestsAllocation

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsAllocation.validated
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsAllocation.separated
