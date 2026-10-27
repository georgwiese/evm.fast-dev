import InitECandidate.Solver.Input.CurrentStartup.RequestsReturned
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual stateless-input caller resumes with the real request record,
its complete ten-field result, and the separately protected payload gas word. -/
structure Result (input : Guest.InputBlob) (caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) (counts : Nat → BitVec 64)
    (value : ValueHOL 64) : Prop where
  context : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength
  rq : current.locals.lookup (ofString "rq") = some (.val (.word requestRecord))
  requestAfter : record.toNat + 136 ≤ requestRecord.toNat
  requestAligned : requestRecord.toNat % 8 = 0
  requestRoom : requestRecord.toNat + 80 ≤ 2952790016
  heap : NormalHeapEffects.AtLeast (requestRecord.toNat + 80) current
  decoded : ∃ entry bodyPost start size,
    RequestsReturned.Result input caller entry bodyPost pointer statelessRecord record gasWord requestRecord payloadLength start size counts ∧
      current.memory = bodyPost.memory
  cells : ∀ index < 5, current.memory (requestRecord + BitVec.ofNat 64 (16 * index + 8)) = .word (counts index)
  locals : current.locals = caller.locals.update (ofString "rq", .val (.word requestRecord))
  returned : evaluateHOLFiniteState current Request.afterRequests = (some (.returned value), post)

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller current post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength : Nat, ∃ counts : Nat → BitVec 64, ∃ value : ValueHOL 64,
      Result input caller current post pointer statelessRecord record gasWord requestRecord payloadLength counts value

/-- Rejoin the complete normally returned request decoder to its genuine
caller continuation, deriving every retained state field from that execution. -/
theorem requests (input : Guest.InputBlob) (actual : RequestsReturned.Reached input) : Reached input := by
  classical
  obtain ⟨caller, entry, bodyPost, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, start, size, counts, data⟩ := actual
  have original := data.origin
  have context := original.context
  obtain ⟨callee, parentPost, value, entryEq, args, called, callerRun⟩ := original.invocation
  have scopedRun := callerRun
  rw [Request.requests_shape.2] at scopedRun
  have positive := CallNormal.normal_clock caller parentPost (ofString "rq") .one (ofString "decode_requests")
    Request.requestsArguments Request.afterRequests value scopedRun
  have bodyRun := data.returned
  rw [entryEq] at bodyRun
  have checked : (shapeEqHOL (shapeOfHOLExact (.val (.word requestRecord) : ValueHOL 64)) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word requestRecord) : ValueHOL 64)) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have invoked := CallNormal.return_execute caller bodyPost "rq" .one (ofString "decode_requests") Request.requestsArguments _
    Requests.body Request.afterRequests callee .one (.val (.word requestRecord)) args called positive bodyRun checked
  have continued := invoked.symm.trans scopedRun
  let current := CallNormal.continuationEntry caller bodyPost "rq" (.val (.word requestRecord))
  have remaining : (evaluateHOLFiniteState current Request.afterRequests).1 = some (.returned value) := congrArg Prod.fst continued
  have fields := evaluation_fields entry bodyPost Requests.body (some (.returned (.val (.word requestRecord)))) data.returned
  have kept (name : String) (different : ofString "rq" ≠ ofString name) :
      current.locals.lookup (ofString name) = caller.locals.lookup (ofString name) := by
    change (caller.locals.update (ofString "rq", .val (.word requestRecord))).lookup (ofString name) = _
    simp [HolFiniteMapExact.update, FUPDATE, different]
  have request : PayloadEntry.CallerLocals input current pointer :=
    ⟨(kept "np" (by decide)).trans context.request.np, (kept "nlen" (by decide)).trans context.request.nlen,
      (kept "o_vh" (by decide)).trans context.request.vh, (kept "o_rq" (by decide)).trans context.request.rq,
      context.request.valid, context.request.upper,
      context.request.outer.preserved (by
        intro name member
        apply kept
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> decide)⟩
  have workspace : current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) := by
    change bodyPost.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64))
    have globalFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) data.control
    have selected := congrArg (fun globals => globals.lookup (ofString "ssz_offs")) globalFrame
    change bodyPost.globals.lookup (ofString "ssz_offs") = _ at selected
    rw [entryEq] at selected
    simpa [WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "ssz_offs" from by decide] using selected.trans context.workspace
  have heap : NormalHeapEffects.AtLeast (record.toNat + 136) current := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := data.heap
    exact ⟨cursor, cell, by have := data.requestAfter; omega, high, aligned⟩
  have currentCode : OriginalCode.Installed current.code := by
    change OriginalCode.Installed bodyPost.code
    rw [fields.2.2.2]
    exact original.code
  have currentShapes : OriginalExceptions.Installed current.eshapes := by
    change OriginalExceptions.Installed bodyPost.eshapes
    rw [fields.2.2.1]
    exact original.shapes
  have currentDomain : current.memaddrs = InitE.ordinaryDomain := fields.1.trans original.domain
  have currentEndian : current.be = false := fields.2.1.trans original.endian
  have readyContext : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength :=
    ⟨currentCode, currentShapes, currentDomain, currentEndian, data.image, heap,
      (kept "pl" (by decide)).trans context.pl, (kept "si" (by decide)).trans context.si,
      context.statelessLower, context.statelessAligned, context.statelessRoom, context.recordAfter, context.recordAligned,
      context.recordRoom, data.gasCell, context.gasBound, context.pointerLower, context.pointerAligned,
      context.inputBound, context.slice, request, workspace⟩
  refine ⟨caller, current, (evaluateHOLFiniteState current Request.afterRequests).2, pointer, statelessRecord, record,
    gasWord, requestRecord, payloadLength, counts, value,
    ⟨readyContext, ?_, data.requestAfter, data.requestAligned, data.requestRoom, data.heap, ⟨entry, bodyPost, start, size, data, rfl⟩,
      (fun index small => (data.cells index small).2), rfl, Prod.ext remaining rfl⟩⟩
  change (caller.locals.update (ofString "rq", .val (.word requestRecord))).lookup (ofString "rq") = _
  simp [HolFiniteMapExact.update, FUPDATE]

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  requests input (RequestsReturned.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn.requests
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn.separated
