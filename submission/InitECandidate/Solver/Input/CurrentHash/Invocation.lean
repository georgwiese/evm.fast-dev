import InitECandidate.Solver.Input.CurrentHash.WorkspaceEffects
import InitECandidate.Solver.Input.CurrentStartup.MainDecodedRequest
import InitECandidate.Solver.Input.CurrentStartup.DecodedRequestsImage
import InitECandidate.Solver.Input.NonTimeoutSequenceCall

namespace InitECandidate.Solver.Input.CurrentHash.Invocation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def values (si out : BitVec 64) : List (ValueHOL 64) := [.val (.word si), .val (.word out)]
def rawLocals (si out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "out" then some (.val (.word out))
  else if name = ofString "si" then some (.val (.word si)) else none

theorem environment (code) (installed : OriginalCode.Installed code) (si out : BitVec 64) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite code.lookup (Code.name .htr_new_payload_request) (values si out) =
        some (Code.body .htr_new_payload_request, callee, .one) ∧
      callee.lookup (ofString "si") = some (.val (.word si)) ∧
      callee.lookup (ofString "out") = some (.val (.word out)) := by
  have formals : Code.formals .htr_new_payload_request = [(ofString "si", .one), (ofString "out", .one)] := by
    simp only [Code.formals, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_new_payload_request, paramToHOL, shapeToHOL, List.map_cons, List.map_nil]
  have shape : Code.shape .htr_new_payload_request = .one := by
    simp only [Code.shape, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_new_payload_request, shapeToHOL]
  have entry : code.lookup (Code.name .htr_new_payload_request) =
      some ([(ofString "si", .one), (ofString "out", .one)], Code.body .htr_new_payload_request, .one) :=
    (Code.installed code installed .htr_new_payload_request).trans (by rw [formals, shape])
  have valid : (([(ofString "si", .one), (ofString "out", .one)] : List (MlS × ShapeHOL)).map Prod.fst).Nodup ∧
      ([(ofString "si", .one), (ofString "out", .one)] : List (MlS × ShapeHOL)).length = (values si out).length ∧
      (([(ofString "si", .one), (ofString "out", .one)] : List (MlS × ShapeHOL)).zip (values si out)).all
        (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true := by
    refine ⟨by decide, rfl, ?_⟩
    simp [values, shapeEqHOL, shapeOfHOLExact]
  have raw : lookupCodeHOLExact code.lookup (Code.name .htr_new_payload_request) (values si out) =
      some (Code.body .htr_new_payload_request, rawLocals si out, .one) := by
    simp only [lookupCodeHOLExact, entry, valid, and_self, ↓reduceIte]
    rfl
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup code.lookup _ _ _ _ .one raw
  exact ⟨callee, called, by rw [locals]; simp [rawLocals, show ofString "si" ≠ ofString "out" from by decide],
    by rw [locals]; simp [rawLocals]⟩

/-- Physical data at the genuine software hasher callee, derived from the
selected main decoder and its actual following root allocation. -/
structure Data (input : Guest.InputBlob) (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer siRecord record requestRecord root array : BitVec 64) (payloadLength start size : Nat) : Prop where
  workspace : WorkspaceEntry.Workspace state
  arena : CurrentStartup.ArenaState state
  payload : Payload.ReturnedImage input state pointer record array payloadLength start size
  heap : NormalHeapEffects.AtLeast (root.toNat + 32) state
  si : state.locals.lookup (ofString "si") = some (.val (.word siRecord))
  out : state.locals.lookup (ofString "out") = some (.val (.word root))
  siArena : AllocatedBytes.Arena siRecord 96
  siAligned : siRecord.toNat % 8 = 0
  rootArena : AllocatedBytes.Arena root 32
  rootAligned : root.toNat % 8 = 0
  rootAfter : max (record.toNat + 136) (requestRecord.toNat + 80) ≤ root.toNat
  arrayBefore : array.toNat + 16 * VarList.decodedCount input start size ≤ root.toNat
  payloadCell : state.memory siRecord = .word record
  hashPointer : state.memory (siRecord + 8#64) = .word (pointer + 18#64 + Request.requestWords input 1)
  hashCount : state.memory (siRecord + 16#64) = .word (BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32))
  header : state.memory (siRecord + 24#64) = .word (pointer + 18#64 + 8#64)
  requests : state.memory (siRecord + 32#64) = .word requestRecord
  requestImage : ∃ requestStart requestSize counts,
    Requests.DecodedImage input state pointer requestRecord requestStart requestSize counts

theorem at_callee {input : Guest.InputBlob} {decoded current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord requestRecord root array : BitVec 64} {payloadLength start size : Nat}
    (ready : RootEntry.Ready input decoded current origin record gasWord requestRecord root array payloadLength start size)
    (workspace : WorkspaceEntry.Workspace current) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (si : callee.lookup (ofString "si") = some (.val (.word origin.word)))
    (out : callee.lookup (ofString "out") = some (.val (.word root))) :
    Data input (callEntryStateHOLFinite current callee) origin.pointer origin.word record requestRecord root array payloadLength start size := by
  have siCell := ready.snapshot.payload_cell
  obtain ⟨hashPointer, hashCount, header, requests⟩ := ready.snapshot.request_fields
  obtain ⟨requestStart,requestSize,counts,requestImage⟩ := ready.snapshot.requests_image
  have actualRequestImage : Requests.DecodedImage input (callEntryStateHOLFinite current callee) origin.pointer requestRecord requestStart requestSize counts :=
    requestImage.of_memory (by intro index inside; exact ⟨congrFun ready.memory _,congrFun ready.memory _⟩)
  obtain ⟨headerSource, headerReady, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    headerStart, headerLength, data, frame, clock⟩ := ready.snapshot
  have siArena : AllocatedBytes.Arena origin.word 96 :=
    ⟨by have := data.context.statelessLower; have := data.context.pointerLower; omega,
      by have := data.context.statelessRoom; omega⟩
  have rootLower : 2701131776 ≤ root.toNat := by
    have := data.context.recordAfter
    have := data.context.statelessLower
    have := data.context.pointerLower
    have := ready.rootAfter
    omega
  refine ⟨workspace.at_callee callee, ⟨ready.arena.scratch, ready.arena.frame, ready.arena.domain, ready.arena.code⟩, ready.payload.of_frame rfl, ready.heap, si, out,
    siArena, data.context.statelessAligned, ⟨rootLower, by have := ready.room; omega⟩,
    ready.aligned, ready.rootAfter, ready.arrayBefore, ?_, ?_, ?_, ?_, ?_, ⟨requestStart,requestSize,counts,actualRequestImage⟩⟩
  all_goals change current.memory _ = _; rw [ready.memory]
  · exact siCell
  · exact hashPointer
  · exact hashCount
  · exact header
  · exact requests

/-- Each real SI load has both its physical stored value and ordinary-domain
mapping. Numeric contents are unrestricted except the proved decoder facts. -/
theorem Data.si_load {input : Guest.InputBlob} {state : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer siRecord record requestRecord root array : BitVec 64} {payloadLength start size : Nat}
    (data : Data input state pointer siRecord record requestRecord root array payloadLength start size)
    (offset : Nat) (inside : offset < 96) (aligned : offset % 8 = 0) (word : BitVec 64)
    (cell : state.memory (siRecord + BitVec.ofNat 64 offset) = .word word) :
    eval state (.load .one (Scalar.plus (localVar "si") offset)) = some (.val (.word word)) :=
  Witness.load_word_read state _ _ word
    (Scalar.plus_read state (localVar "si") siRecord offset (Request.local_word state "si" siRecord data.si))
    (AllocatedBytes.word_mapped state siRecord 96 offset data.workspace.domain data.siArena inside data.siAligned aligned) cell

/-- A non-timeout observation of the actual enclosing main suffix reaches
this same callee. Funding and its non-timeout result follow from that observation. -/
theorem call_trace {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord requestRecord root array : BitVec 64} {payloadLength start size : Nat}
    (ready : RootEntry.Ready input decoded current origin record gasWord requestRecord root array payloadLength start size)
    (workspace : WorkspaceEntry.Workspace current) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState current RootEntry.afterRoot = (result, post)) (notTimeout : result ≠ some .timeOut) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite current.code.lookup (Code.name .htr_new_payload_request) (values origin.word root) =
        some (Code.body .htr_new_payload_request, callee, .one) ∧
      Data input (callEntryStateHOLFinite current callee) origin.pointer origin.word record requestRecord root array payloadLength start size ∧
      1 ≤ current.clock ∧ (evaluateHOLFiniteState (callEntryStateHOLFinite current callee) (Code.body .htr_new_payload_request)).1 ≠ some .timeOut := by
  obtain ⟨callee, called, si, out⟩ := environment current.code workspace.code origin.word root
  rw [RootEntry.after_shape] at actual
  obtain ⟨funded, notTimeout⟩ := sequence_call_non_timeout current post (some (none, none)) (Code.name .htr_new_payload_request)
    RootEntry.arguments (values origin.word root) (Code.body .htr_new_payload_request) HashPrefix.afterHash callee .one
    ready.args called result actual notTimeout
  exact ⟨callee, called, at_callee ready workspace callee si out, funded, notTimeout⟩

end InitECandidate.Solver.Input.CurrentHash.Invocation

#print axioms InitECandidate.Solver.Input.CurrentHash.Invocation.environment
#print axioms InitECandidate.Solver.Input.CurrentHash.Invocation.at_callee
#print axioms InitECandidate.Solver.Input.CurrentHash.Invocation.Data.si_load
#print axioms InitECandidate.Solver.Input.CurrentHash.Invocation.call_trace
