import InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual caller state after decode_payload, including allocation ownership
and the bounded physical gas cell needed by later main/attempt execution. -/
structure Context (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length : Nat) : Prop where
  code : OriginalCode.Installed current.code
  shapes : OriginalExceptions.Installed current.eshapes
  domain : current.memaddrs = InitE.ordinaryDomain
  endian : current.be = false
  image : Blob.HeapInput current input pointer
  heap : NormalHeapEffects.AtLeast (record.toNat + 136) current
  pl : current.locals.lookup (ofString "pl") = some (.val (.word record))
  si : current.locals.lookup (ofString "si") = some (.val (.word statelessRecord))
  statelessLower : pointer.toNat + input.length % 2^64 + 8 ≤ statelessRecord.toNat
  statelessAligned : statelessRecord.toNat % 8 = 0
  statelessRoom : statelessRecord.toNat + 96 ≤ 2952790016
  recordAfter : statelessRecord.toNat + 96 ≤ record.toNat
  recordAligned : record.toNat % 8 = 0
  recordRoom : record.toNat + 136 ≤ 2952790016
  gasCell : current.memory (record + 88#64) = .word gasWord
  gasBound : gasWord.toNat ≤ 200000000
  pointerLower : 2701134640 ≤ pointer.toNat
  pointerAligned : pointer.toNat % 8 = 0
  inputBound : input.length % 2^64 ≤ Guest.maxInputBytes
  slice : length = Guest.GasLimit.le32 input 22 - 44
  request : PayloadEntry.CallerLocals input current pointer
  workspace : current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64))

structure Result (input : Guest.InputBlob) (caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length : Nat) (value : ValueHOL 64) : Prop where
  context : Context input current pointer statelessRecord record gasWord length
  locals : current.locals = caller.locals.update (ofString "pl", .val (.word record))
  returned : evaluateHOLFiniteState current Request.afterPayload = (some (.returned value), post)

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller current post, ∃ pointer statelessRecord record gasWord : BitVec 64, ∃ length : Nat, ∃ value : ValueHOL 64,
    Result input caller current post pointer statelessRecord record gasWord length value

/-- Reinstall the real payload pointer in the actual request caller and
resume its existing continuation. The two record allocations are disjoint. -/
theorem withdrawal (input : Guest.InputBlob) (actual : WithdrawalReturn.Reached input)
    (gas : (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)).toNat ≤ 200000000) : Reached input := by
  classical
  obtain ⟨entry, bodyPost, pointer, record, length, originHeap, original, bodyRun, image, gasCell, heap⟩ :=
    PayloadGasReturned.complete input actual
  obtain ⟨lengthBound, installed, shapes, domain, endian, entryImage, entryHeap, workspace, lower, aligned, room,
    p, n, extent, minimum, sliceUpper, sliceEq, afterRun, invocation⟩ := original
  obtain ⟨caller, callee, parentPost, value, statelessRecord, entryEq, statelessLower, statelessAligned,
    statelessRoom, si, requestHeap, callerLocals, args, called, callerRun⟩ := invocation
  have positiveRun := callerRun
  rw [Request.payload_call_shape] at positiveRun
  have positive := CallNormal.normal_clock caller parentPost (ofString "pl") .one (ofString "decode_payload")
    Request.payloadArguments Request.afterPayload value positiveRun
  have offsetFrame := OffsetsFrame.decode_payload entry.code installed entry rfl
  have literalBody : Code.body .decode_payload = Payload.body := rfl
  rw [literalBody, bodyRun] at offsetFrame
  have currentWorkspace : bodyPost.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) :=
    (congrArg Prod.snd offsetFrame).trans workspace
  rw [entryEq] at bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact (.val (.word record) : ValueHOL 64)) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word record) : ValueHOL 64)) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have invoked := CallNormal.return_execute caller bodyPost "pl" .one (ofString "decode_payload") Request.payloadArguments _
    Payload.body Request.afterPayload callee .one (.val (.word record)) args called positive bodyRun shapePass
  have continued := invoked.symm.trans positiveRun
  let current := CallNormal.continuationEntry caller bodyPost "pl" (.val (.word record))
  have remaining : (evaluateHOLFiniteState current Request.afterPayload).1 = some (.returned value) := congrArg Prod.fst continued
  have fields := evaluation_fields (callEntryStateHOLFinite caller callee) bodyPost Payload.body (some (.returned (.val (.word record)))) bodyRun
  have currentCode : OriginalCode.Installed current.code := by
    change OriginalCode.Installed bodyPost.code
    rw [fields.2.2.2, ← entryEq]
    exact installed
  have currentShapes : OriginalExceptions.Installed current.eshapes := by
    change OriginalExceptions.Installed bodyPost.eshapes
    rw [fields.2.2.1, ← entryEq]
    exact shapes
  obtain ⟨cursor, cursorCell, recordAfter, cursorBound, cursorAligned⟩ := requestHeap
  have cursorEq : cursor = record := by
    have eq := Option.some.inj (cursorCell.symm.trans originHeap)
    cases eq
    rfl
  subst cursor
  have recordRoom : record.toNat + 136 ≤ 2952790016 := by
    obtain ⟨frontier, cell, low, high, frontierAligned⟩ := heap
    omega
  refine ⟨caller, current, (evaluateHOLFiniteState current Request.afterPayload).2, pointer, statelessRecord, record,
    BitVec.ofNat 64 (Guest.GasLimit.le64 input 474), length, value,
    ⟨⟨currentCode, currentShapes, ?_, ?_, Blob.HeapInput.of_fields bodyPost current input pointer rfl rfl rfl image,
      heap, ?_, ?_, statelessLower, statelessAligned, statelessRoom, recordAfter, cursorAligned, recordRoom,
      gasCell, gas, lower, aligned, lengthBound, sliceEq, ?_, currentWorkspace⟩, rfl, Prod.ext remaining rfl⟩⟩
  · change bodyPost.memaddrs = InitE.ordinaryDomain
    rw [fields.1, ← entryEq]
    exact domain
  · change bodyPost.be = false
    rw [fields.2.1, ← entryEq]
    exact endian
  · change (caller.locals.update (ofString "pl", .val (.word record))).lookup (ofString "pl") = _
    simp [HolFiniteMapExact.update, FUPDATE]
  · change (caller.locals.update (ofString "pl", .val (.word record))).lookup (ofString "si") = _
    simpa [HolFiniteMapExact.update, FUPDATE, show ofString "pl" ≠ ofString "si" from by decide] using si
  · have kept (name : String) (other : ofString "pl" ≠ ofString name) :
        current.locals.lookup (ofString name) = caller.locals.lookup (ofString name) := by
      change (caller.locals.update (ofString "pl", .val (.word record))).lookup (ofString name) = _
      simp [HolFiniteMapExact.update, FUPDATE, other]
    exact ⟨(kept "np" (by decide)).trans callerLocals.np, (kept "nlen" (by decide)).trans callerLocals.nlen,
      (kept "o_vh" (by decide)).trans callerLocals.vh, (kept "o_rq" (by decide)).trans callerLocals.rq, callerLocals.valid⟩

/-- Memory/clock changes retain the request context when original input
and the actual gas cell are separately preserved. -/
theorem Context.memory_clock (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length clock : Nat) (memory : BitVec 64 → HolWordLab 64)
    (context : Context input source pointer statelessRecord record gasWord length)
    (image : Blob.HeapInput {source with memory := memory, clock := clock} input pointer)
    (gas : memory (record + 88#64) = .word gasWord) :
    Context input {source with memory := memory, clock := clock} pointer statelessRecord record gasWord length :=
  ⟨context.code, context.shapes, context.domain, context.endian, image, context.heap, context.pl, context.si,
    context.statelessLower, context.statelessAligned, context.statelessRoom, context.recordAfter, context.recordAligned,
    context.recordRoom, gas, context.gasBound, context.pointerLower, context.pointerAligned, context.inputBound,
    context.slice, ⟨context.request.np, context.request.nlen, context.request.vh, context.request.rq, context.request.valid⟩, context.workspace⟩

/-- A real scalar field store to the earlier stateless record preserves the
separate payload gas cell and original input, using derived allocation bounds. -/
theorem Context.stateless_store (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length offset : Nat) (expression : ExpHOL 64) (word : BitVec 64)
    (context : Context input source pointer statelessRecord record gasWord length)
    (inside : offset ≤ 88) (aligned : offset % 8 = 0)
    (read : eval source expression = some (.val (.word word))) :
    let target := {source with memory := WitnessRadix.StoreWord.put source.memory (statelessRecord + BitVec.ofNat 64 offset) word}
    evaluateHOLFiniteState source (.store (Scalar.plus (localVar "si") offset) expression) = (none, target) ∧
      Context input target pointer statelessRecord record gasWord length := by
  classical
  have encoded : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have number : (statelessRecord + BitVec.ofNat 64 offset).toNat = statelessRecord.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; have := context.statelessRoom; omega), encoded]
  have mapped : source.memaddrs (statelessRecord + BitVec.ofNat 64 offset) := by
    rw [context.domain]
    apply WitnessRadix.BackingLayout.ordinary_mapped
    · rw [number]; have := context.statelessLower; have := context.pointerLower; omega
    · rw [number]; have := context.statelessRoom; omega
    · rw [number]; have := context.statelessAligned; omega
  have address := Scalar.plus_read source (localVar "si") statelessRecord offset (Request.local_word source "si" statelessRecord context.si)
  have run := WitnessRadix.StoreWord.execute source _ expression _ word address read mapped
  have image := Blob.HeapInput.store_separate source input pointer _ word context.image context.pointerAligned
    (by have := context.statelessLower; have := context.statelessRoom; omega) (Or.inr (by rw [number]; have := context.statelessLower; omega))
  have gasNumber : (record + 88#64).toNat = record.toNat + 88 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 88 < 2^64; have := context.recordRoom; omega)]
    rfl
  have separate : record + 88#64 ≠ statelessRecord + BitVec.ofNat 64 offset := by
    intro same
    have natural := congrArg BitVec.toNat same
    rw [number, gasNumber] at natural
    have := context.recordAfter
    omega
  have gas : WitnessRadix.StoreWord.put source.memory (statelessRecord + BitVec.ofNat 64 offset) word (record + 88#64) = .word gasWord := by
    simpa [WitnessRadix.StoreWord.put, separate] using context.gasCell
  exact ⟨run, Context.memory_clock input source pointer statelessRecord record gasWord length source.clock _ context image gas⟩

/-- A pure returned call preserves the payload ownership and physical gas
cell. Only the retained local bindings need separate caller-scope evidence. -/
theorem Context.of_frame (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length : Nat)
    (context : Context input source pointer statelessRecord record gasWord length)
    (frame : LocalEffects.erase target = LocalEffects.erase source)
    (pl : target.locals.lookup (ofString "pl") = some (.val (.word record)))
    (si : target.locals.lookup (ofString "si") = some (.val (.word statelessRecord)))
    (request : PayloadEntry.CallerLocals input target pointer) :
    Context input target pointer statelessRecord record gasWord length := by
  have stateEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    {state with locals := target.locals, clock := target.clock}) frame
  change target = {source with locals := target.locals, clock := target.clock} at stateEq
  rw [stateEq] at pl si request ⊢
  exact ⟨context.code, context.shapes, context.domain, context.endian, context.image, context.heap, pl, si,
    context.statelessLower, context.statelessAligned, context.statelessRoom, context.recordAfter, context.recordAligned,
    context.recordRoom, context.gasCell, context.gasBound, context.pointerLower, context.pointerAligned,
    context.inputBound, context.slice, request, context.workspace⟩

/-- The shared pure-call frame with one fresh caller binding, including all
live request locals. Distinctness is checked at each actual named call. -/
theorem Context.bind_frame (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length : Nat) (name : MlS) (value : ValueHOL 64)
    (context : Context input source pointer statelessRecord record gasWord length)
    (frame : LocalEffects.erase target = LocalEffects.erase source)
    (locals : target.locals = source.locals.update (name, value))
    (different : name ∉ [ofString "pl", ofString "si", ofString "np", ofString "nlen", ofString "o_vh", ofString "o_rq"]) :
    Context input target pointer statelessRecord record gasWord length := by
  classical
  have kept (key : MlS) (member : key ∈ [ofString "pl", ofString "si", ofString "np", ofString "nlen", ofString "o_vh", ofString "o_rq"]) :
      target.locals.lookup key = source.locals.lookup key := by
    have other : name ≠ key := by intro same; apply different; rw [same]; exact member
    rw [locals]
    simp [HolFiniteMapExact.update, FUPDATE, other]
  exact Context.of_frame input source target pointer statelessRecord record gasWord length context frame
    ((kept (ofString "pl") (by simp)).trans context.pl) ((kept (ofString "si") (by simp)).trans context.si)
    ⟨(kept (ofString "np") (by simp)).trans context.request.np, (kept (ofString "nlen") (by simp)).trans context.request.nlen,
      (kept (ofString "o_vh") (by simp)).trans context.request.vh, (kept (ofString "o_rq") (by simp)).trans context.request.rq,
      context.request.valid⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input := by
  obtain ⟨request, payload⟩ := CanonicalRequest.separated_offsets input word actual
  exact withdrawal input (WithdrawalReturn.separated input word actual) (Payload.stored_gas_bound input request payload gas)

end InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.withdrawal
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.separated

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.Context.of_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.Context.bind_frame

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.Context.memory_clock
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.Context.stateless_store
