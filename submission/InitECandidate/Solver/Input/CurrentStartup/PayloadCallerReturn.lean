import InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual caller state after decode_payload, including allocation ownership
and the bounded physical gas cell needed by later main/attempt execution. -/
structure Result (input : Guest.InputBlob) (caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length : Nat) (value : ValueHOL 64) : Prop where
  code : OriginalCode.Installed current.code
  shapes : OriginalExceptions.Installed current.eshapes
  domain : current.memaddrs = InitE.ordinaryDomain
  endian : current.be = false
  image : Blob.HeapInput current input pointer
  heap : NormalHeapEffects.AtLeast (record.toNat + 136) current
  locals : current.locals = caller.locals.update (ofString "pl", .val (.word record))
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
    statelessRoom, si, requestHeap, args, called, callerRun⟩ := invocation
  have positiveRun := callerRun
  rw [Request.payload_call_shape] at positiveRun
  have positive := CallNormal.normal_clock caller parentPost (ofString "pl") .one (ofString "decode_payload")
    Request.payloadArguments Request.afterPayload value positiveRun
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
    ⟨currentCode, currentShapes, ?_, ?_, Blob.HeapInput.of_fields bodyPost current input pointer rfl rfl rfl image,
      heap, rfl, ?_, ?_, statelessLower, statelessAligned, statelessRoom, recordAfter, cursorAligned, recordRoom,
      gasCell, gas, lower, aligned, lengthBound, sliceEq, Prod.ext remaining rfl⟩⟩
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

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input := by
  obtain ⟨request, payload⟩ := CanonicalRequest.separated_offsets input word actual
  exact withdrawal input (WithdrawalReturn.separated input word actual) (Payload.stored_gas_bound input request payload gas)

end InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.withdrawal
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.separated
