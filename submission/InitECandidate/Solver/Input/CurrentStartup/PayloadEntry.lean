import InitECandidate.Solver.Input.CurrentStartup.CanonicalRequest
import InitECandidate.Solver.Input.PayloadCalleeNormal

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Live validated request bindings retained by subsequent decoder calls. -/
structure CallerLocals (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) : Prop where
  np : current.locals.lookup (ofString "np") = some (.val (.word (pointer + 18#64)))
  nlen : current.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16))))
  vh : current.locals.lookup (ofString "o_vh") = some (.val (.word (Request.requestWords input 1)))
  rq : current.locals.lookup (ofString "o_rq") = some (.val (.word (Request.requestWords input 2)))
  valid : ∀ position < 3, Offsets.ValidAt 44#64 (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)) (Request.requestWords input) position

/-- Entry facts for the actual complete payload return, indexed by its states. -/
def Result (input : Guest.InputBlob) (entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (length : Nat) (returned : ValueHOL 64) : Prop :=
    input.length % 2^64 ≤ Guest.maxInputBytes ∧ OriginalCode.Installed entry.code ∧
    OriginalExceptions.Installed entry.eshapes ∧ entry.memaddrs = InitE.ordinaryDomain ∧ entry.be = false ∧
    Blob.HeapInput entry input pointer ∧ NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) entry ∧
    entry.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) ∧
    2701134640 ≤ pointer.toNat ∧ pointer.toNat % 8 = 0 ∧ pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016 ∧
    entry.locals.lookup (ofString "p") = some (.val (.word (pointer + 62#64))) ∧
    entry.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) ∧
    602 ≤ input.length % 2^64 ∧ 540 ≤ length ∧ length ≤ input.length % 2^64 - 62 ∧
    length = Guest.GasLimit.le32 input 22 - 44 ∧
    evaluateHOLFiniteState entry Payload.afterGuard = (some (.returned returned), post) ∧
    ∃ caller callee parentPost parentValue, ∃ statelessRecord : BitVec 64,
      entry = callEntryStateHOLFinite caller callee ∧
      pointer.toNat + input.length % 2^64 + 8 ≤ statelessRecord.toNat ∧ statelessRecord.toNat % 8 = 0 ∧
      statelessRecord.toNat + 96 ≤ 2952790016 ∧
      caller.locals.lookup (ofString "si") = some (.val (.word statelessRecord)) ∧
      NormalHeapEffects.AtLeast (statelessRecord.toNat + 96) entry ∧ CallerLocals input caller pointer ∧
      evalListHOLFinite caller (h := fun address => Classical.propDecidable (caller.memaddrs address)) Request.payloadArguments =
        some (Payload.values (pointer + 62#64) (BitVec.ofNat 64 length)) ∧
      lookupCodeHOLFinite caller.code.lookup (ofString "decode_payload")
        (Payload.values (pointer + 62#64) (BitVec.ofNat 64 length)) = some (Payload.body, callee, .one) ∧
      evaluateHOLFiniteState caller Request.continuation = (some (.returned parentValue), parentPost)

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ entry post, ∃ pointer : BitVec 64, ∃ length : Nat, ∃ returned : ValueHOL 64,
    Result input entry post pointer length returned

/-- A later returned suffix has the same nonlocal result as the complete
payload entry. This remembers the actual endpoint through lexical restoration. -/
def Endpoint (input : Guest.InputBlob) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) (length : Nat) (value : ValueHOL 64) : Prop :=
  ∃ entry payloadPost, Result input entry payloadPost pointer length value ∧
    entry.globals.lookup (ofString "heap_ptr") = some (.val (.word record)) ∧ LocalEffects.erase payloadPost = LocalEffects.erase post ∧ payloadPost.clock = post.clock

theorem Endpoint.of_frame (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) (length : Nat) (value : ValueHOL 64)
    (original : Endpoint input source pointer record length value)
    (frame : LocalEffects.erase source = LocalEffects.erase target) (clock : source.clock = target.clock) :
    Endpoint input target pointer record length value := by
  obtain ⟨entry, post, actual, cell, originalFrame, originalClock⟩ := original
  exact ⟨entry, post, actual, cell, originalFrame.trans frame, originalClock.trans clock⟩

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "decode_payload") = some (Payload.formals, Payload.body, .one) := by
  simpa only [Code.name, Code.body, Code.formals, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_decode_payload, Payload.formals, Payload.body, Scalar.payloadBody,
    shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
    using Code.installed code installed .decode_payload

/-- Actual request return reaches the genuine payload callee at input+62.
Its length guard derives the540-byte slice and602-byte encoded extent; copied
bytes and allocator frontier survive the real offset writes and call entry. -/
theorem request_reached (input : Guest.InputBlob) (word : BitVec 64)
    (actual : RecordEntry.Reached input word) : Reached input := by
  obtain ⟨source, post, pointer, record, lengthBound, installed, shapes, domain, endian, image, heap,
    workspace, lower, aligned, room, recordLower, recordAligned, recordRoom, recordHeap, si, np, nlen, extent, requestLower, requestUpper, returned⟩ := actual
  rcases Request.offsets_trace source post input pointer 2701132528#64 (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16))
    image extent np nlen workspace domain aligned (by decide) (by omega) (by decide)
    (by change 2701132528 + 64 ≤ pointer.toNat; omega)
    (CanonicalHeader.offset_code source.code installed) (CanonicalHeader.fail_code source.code installed) (shapes .SszErr)
    (some (.returned (.val (.word word)))) returned (by simp) with fault | continued
  · obtain ⟨error, allowed, impossible, paid⟩ := fault
    cases impossible
  · obtain ⟨first, valid, next, inner, paid, bound, funded, nextEq, retained, remaining, restored⟩ := continued
    obtain ⟨rawFirst, hashLower, ordered, requestEnd⟩ := Request.request_values input _ first valid
    have witnessSmall := Framing.le32_lt input 6
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at requestEnd
    have hashUpper : Guest.GasLimit.le32 input 22 ≤ input.length % 2^64 - 18 := by omega
    have nextNp : next.locals.lookup (ofString "np") = some (.val (.word (pointer + 18#64))) := by
      rw [nextEq]
      exact (bind_lookup_other _ "o_rq" "np" _ (by decide)).trans
        ((bind_lookup_other _ "o_vh" "np" _ (by decide)).trans ((bind_lookup_other _ "o_pl" "np" _ (by decide)).trans np))
    have nextPl : next.locals.lookup (ofString "o_pl") = some (.val (.word (Request.requestWords input 0))) := by
      rw [nextEq]
      exact (bind_lookup_other _ "o_rq" "o_pl" _ (by decide)).trans
        ((bind_lookup_other _ "o_vh" "o_pl" _ (by decide)).trans (bind_lookup_same _ _ _))
    have nextVh : next.locals.lookup (ofString "o_vh") = some (.val (.word (Request.requestWords input 1))) := by
      rw [nextEq]
      exact (bind_lookup_other _ "o_rq" "o_vh" _ (by decide)).trans (bind_lookup_same _ _ _)
    obtain ⟨args, sliceUpper⟩ := Request.payload_arguments next input pointer nextNp nextPl nextVh rawFirst hashLower hashUpper extent
    have nextCode : next.code = source.code := by rw [nextEq]; rfl
    have nextShapes : next.eshapes = source.eshapes := by rw [nextEq]; rfl
    have nextDomain : next.memaddrs = source.memaddrs := by rw [nextEq]; rfl
    have nextEndian : next.be = source.be := by rw [nextEq]; rfl
    have nextGlobals : next.globals = source.globals := by rw [nextEq]; rfl
    have callerRun := remaining
    rw [Request.payload_call_shape] at remaining
    have positive := CallNormal.normal_clock next inner (ofString "pl") .one (ofString "decode_payload")
      Request.payloadArguments Request.afterPayload (.val (.word word)) remaining
    obtain ⟨callee, called, pCell, lenCell, bodyPost, value, bodyRun⟩ := Payload.callee_normal next inner Request.payloadArguments Request.afterPayload
      (pointer + 62#64) (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22 - 44)) args
      (by rw [nextCode]; exact original_code source.code installed) positive (.val (.word word)) remaining
    have nextNlen : next.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)))) := by
      rw [nextEq]
      exact (bind_lookup_other _ "o_rq" "nlen" _ (by decide)).trans
        ((bind_lookup_other _ "o_vh" "nlen" _ (by decide)).trans ((bind_lookup_other _ "o_pl" "nlen" _ (by decide)).trans nlen))
    have nextRq : next.locals.lookup (ofString "o_rq") = some (.val (.word (Request.requestWords input 2))) := by
      rw [nextEq]
      exact bind_lookup_same _ _ _
    have callerLocals : CallerLocals input next pointer := ⟨nextNp, nextNlen, nextVh, nextRq, valid⟩
    have nextSi : next.locals.lookup (ofString "si") = some (.val (.word record)) := by
      rw [nextEq]
      exact (bind_lookup_other _ "o_rq" "si" _ (by decide)).trans
        ((bind_lookup_other _ "o_vh" "si" _ (by decide)).trans ((bind_lookup_other _ "o_pl" "si" _ (by decide)).trans si))
    let entry := callEntryStateHOLFinite next callee
    have sliceNumber : (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22 - 44)).toNat = Guest.GasLimit.le32 input 22 - 44 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Framing.le32_lt input 22; omega)]
    have read := Payload.length_test_read entry (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22 - 44)) lenCell
    rw [Payload.body_shape] at bodyRun
    obtain ⟨minimum, after⟩ := guard_actual entry bodyPost Payload.lengthTest 50#64
      ((BitVec.ofNat 64 (Guest.GasLimit.le32 input 22 - 44)).toNat < 540) read
      (by change next.code.lookup _ = _; rw [nextCode]; exact CanonicalHeader.fail_code source.code installed)
      (by change next.eshapes.lookup _ = _; rw [nextShapes]; exact shapes .SszErr) Payload.afterGuard value bodyRun
    rw [sliceNumber] at minimum
    have entryCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed next.code; rw [nextCode]; exact installed
    have entryShapes : OriginalExceptions.Installed entry.eshapes := by change OriginalExceptions.Installed next.eshapes; rw [nextShapes]; exact shapes
    have entryBytes : Blob.HeapInput entry input pointer := Blob.HeapInput.of_fields next entry input pointer rfl rfl rfl retained
    have entryHeap : NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) entry := by
      obtain ⟨cursor, cell, low, high, aligned⟩ := heap
      exact ⟨cursor, (congrArg (fun globals => globals.lookup (ofString "heap_ptr")) nextGlobals).trans cell, low, high, aligned⟩
    have entryRecordHeap : NormalHeapEffects.AtLeast (record.toNat + 96) entry := by
      obtain ⟨cursor, cell, low, high, cursorAligned⟩ := recordHeap
      exact ⟨cursor, (congrArg (fun globals => globals.lookup (ofString "heap_ptr")) nextGlobals).trans cell, low, high, cursorAligned⟩
    refine ⟨entry, bodyPost, pointer, Guest.GasLimit.le32 input 22 - 44, value, lengthBound, entryCode, entryShapes,
      nextDomain.trans domain, nextEndian.trans endian, entryBytes, entryHeap, ?_, lower, aligned, room, pCell, lenCell,
      (by omega), (by omega), sliceUpper, rfl, after, next, callee, inner, .val (.word word), record, rfl, recordLower, recordAligned, recordRoom, nextSi, entryRecordHeap, callerLocals, args, called, callerRun⟩
    exact (congrArg (fun globals => globals.lookup (ofString "ssz_offs")) nextGlobals).trans workspace

theorem separated (input : Guest.InputBlob) (word : BitVec 64) (actual : MainSeparatedInput.StatelessRun input word) : Reached input :=
  request_reached input word (RecordEntry.separated input word actual)

end InitECandidate.Solver.Input.CurrentStartup.PayloadEntry

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadEntry.original_code
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadEntry.request_reached
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadEntry.separated

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadEntry.Endpoint.of_frame
