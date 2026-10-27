import InitECandidate.Solver.Input.CurrentStartup.HashCountReturn
import InitECandidate.Solver.Input.RequestRequestsProgram

namespace InitECandidate.Solver.Input.CurrentStartup.RequestsEntry
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (caller entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (payloadLength start size : Nat) (value : ValueHOL 64) : Prop where
  context : PayloadCallerReturn.Context input caller pointer statelessRecord record gasWord payloadLength
  code : OriginalCode.Installed entry.code
  shapes : OriginalExceptions.Installed entry.eshapes
  domain : entry.memaddrs = InitE.ordinaryDomain
  endian : entry.be = false
  image : Blob.HeapInput entry input pointer
  heap : NormalHeapEffects.AtLeast (record.toNat + 136) entry
  p : entry.locals.lookup (ofString "p") = some (.val (.word (pointer + BitVec.ofNat 64 start)))
  len : entry.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 size)))
  startEq : start = 18 + Guest.GasLimit.le32 input 58
  sizeEq : size = Guest.GasLimit.le32 input 6 - 16 - Guest.GasLimit.le32 input 58
  inside : start + size ≤ input.length % 2^64
  minimum : 20 ≤ size
  returned : evaluateHOLFiniteState entry Requests.afterGuard = (some (.returned value), post)
  invocation : ∃ callee parentPost parentValue,
    entry = callEntryStateHOLFinite caller callee ∧
    evalListHOLFinite caller (h := fun address => Classical.propDecidable (caller.memaddrs address)) Request.requestsArguments =
      some (Requests.values (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 size)) ∧
    lookupCodeHOLFinite caller.code.lookup (ofString "decode_requests")
      (Requests.values (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 size)) = some (Requests.body, callee, .one) ∧
    evaluateHOLFiniteState caller Request.requestsCall = (some (.returned parentValue), parentPost)
  history : ∃ origin hashSource hashPost count parentValue first second,
    HashCountReturn.Result (decoderOrigin := decoderOrigin) input origin hashSource hashPost pointer statelessRecord record gasWord count payloadLength parentValue ∧
    evaluateHOLFiniteState caller Request.requestsCall = (some (.returned parentValue), hashPost) ∧
    evaluateHOLFiniteState hashSource Request.hashPointerStore = (none, first) ∧
    evaluateHOLFiniteState first Request.hashCountStore = (none, second) ∧
    evaluateHOLFiniteState second Request.requestHeaderStore = (none, caller)

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller entry post, ∃ pointer statelessRecord record gasWord : BitVec 64, ∃ payloadLength start size : Nat, ∃ value : ValueHOL 64,
    Result (decoderOrigin := decoderOrigin) input caller entry post pointer statelessRecord record gasWord payloadLength start size value

/-- Actual hash metadata stores then the real request decoder and its passing
length guard. Input containment, allocation frontier and gas protection derive
from the already reached request caller and its original validated offsets. -/
theorem hashes (input : Guest.InputBlob) (actual : HashCountReturn.Reached (decoderOrigin := decoderOrigin) input) : Reached (decoderOrigin := decoderOrigin) input := by
  classical
  obtain ⟨origin, source, post, pointer, statelessRecord, record, gasWord, count, payloadLength, value, data⟩ := actual
  have context := data.context
  have firstRead : eval source (.op .add [localVar "np", localVar "o_vh"]) =
      some (.val (.word (pointer + 18#64 + Request.requestWords input 1))) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, context.request.np, context.request.vh,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨firstRun, firstContext⟩ := context.stateless_store input source pointer statelessRecord record gasWord payloadLength 8
    (.op .add [localVar "np", localVar "o_vh"]) _ (by decide) (by decide) firstRead
  let first := {source with memory := WitnessRadix.StoreWord.put source.memory (statelessRecord + 8#64) (pointer + 18#64 + Request.requestWords input 1)}
  have countCell : first.locals.lookup (ofString "nvh") = some (.val (.word count)) := data.nvh
  obtain ⟨secondRun, secondContext⟩ := firstContext.stateless_store input first pointer statelessRecord record gasWord payloadLength 16
    (localVar "nvh") count (by decide) (by decide) (Request.local_word first "nvh" count countCell)
  let second := {first with memory := WitnessRadix.StoreWord.put first.memory (statelessRecord + 16#64) count}
  have headerRead := Scalar.plus_read second (localVar "np") (pointer + 18#64) 8
    (Request.local_word second "np" _ secondContext.request.np)
  obtain ⟨thirdRun, callerContext⟩ := secondContext.stateless_store input second pointer statelessRecord record gasWord payloadLength 24
    (Scalar.plus (localVar "np") 8) _ (by decide) (by decide) headerRead
  let caller := {second with memory := WitnessRadix.StoreWord.put second.memory (statelessRecord + 24#64) (pointer + 18#64 + 8#64)}
  change evaluateHOLFiniteState source Request.hashPointerStore = (none, first) at firstRun
  change evaluateHOLFiniteState first Request.hashCountStore = (none, second) at secondRun
  change evaluateHOLFiniteState second Request.requestHeaderStore = (none, caller) at thirdRun
  have callerRun := data.returned
  rw [Request.requests_shape.1,
    WitnessRadix.StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence second caller _ _ thirdRun (Nat.le_refl _)] at callerRun
  have last := callerContext.request.valid 2 (by decide)
  have upper := last.2.1
  change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 58)).toNat ≤ (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)).toNat at upper
  have totalNat : (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)).toNat = Guest.GasLimit.le32 input 6 - 16 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Framing.le32_lt input 6; omega)]
  rw [Request.le32_number input 58 (by decide), totalNat] at upper
  have lower := last.1
  change 44 ≤ (BitVec.ofNat 64 (Guest.GasLimit.le32 input 58)).toNat at lower
  rw [Request.le32_number input 58 (by decide)] at lower
  let start := 18 + Guest.GasLimit.le32 input 58
  let size := Guest.GasLimit.le32 input 6 - 16 - Guest.GasLimit.le32 input 58
  have inside : start + size ≤ input.length % 2^64 := by
    have bound := callerContext.request.upper
    dsimp only [start, size]
    omega
  have subtraction := BitVec.ofNat_sub_ofNat_of_le (w := 64) (Guest.GasLimit.le32 input 6 - 16) (Guest.GasLimit.le32 input 58)
    (by have := Framing.le32_lt input 58; omega) upper
  have np : caller.locals.lookup (ofString "np") = some (.val (.word (pointer + 18#64))) := callerContext.request.np
  have nlen : caller.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16)))) := callerContext.request.nlen
  have rq : caller.locals.lookup (ofString "o_rq") = some (.val (.word (Request.requestWords input 2))) := callerContext.request.rq
  have args : evalListHOLFinite caller (h := fun address => Classical.propDecidable (caller.memaddrs address)) Request.requestsArguments =
      some (Requests.values (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 size)) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, Request.requestsArguments, Requests.values,
      localVar, np, nlen, rq, Request.requestWords,
      valueIsWord, valueWord, wordOpHOL, wordOp, start, size, BitVec.add_assoc, ← BitVec.ofNat_add, subtraction]
  obtain ⟨callee, called, p, n⟩ := Requests.environment caller.code.lookup (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 size)
    (Requests.original_code caller.code callerContext.code)
  have scopedRun := callerRun
  rw [Request.requests_shape.2] at scopedRun
  have positive := CallNormal.normal_clock caller post (ofString "rq") .one (ofString "decode_requests") Request.requestsArguments Request.afterRequests value scopedRun
  obtain ⟨bodyPost, returned, bodyRun⟩ := CallNormal.callee_return caller post (ofString "rq") .one (ofString "decode_requests")
    Request.requestsArguments _ Requests.body Request.afterRequests callee .one args called positive value scopedRun
  let entry := callEntryStateHOLFinite caller callee
  have test := Requests.length_test_read entry (BitVec.ofNat 64 size) n
  rw [Requests.guard_shape] at bodyRun
  obtain ⟨large, remaining⟩ := guard_actual entry bodyPost Requests.shortTest 60#64 ((BitVec.ofNat 64 size).toNat < 20) test
    (CanonicalHeader.fail_code entry.code callerContext.code) (callerContext.shapes .SszErr) Requests.afterGuard returned bodyRun
  have sizeNat : (BitVec.ofNat 64 size).toNat = size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.mod_lt input.length (show 0 < 2^64 by decide); omega)]
  rw [sizeNat] at large
  exact ⟨caller, entry, bodyPost, pointer, statelessRecord, record, gasWord, payloadLength, start, size, returned,
    ⟨callerContext, callerContext.code, callerContext.shapes, callerContext.domain, callerContext.endian,
      Blob.HeapInput.of_fields caller entry input pointer rfl rfl rfl callerContext.image, callerContext.heap,
      p, n, rfl, rfl, inside, by omega, remaining,
      ⟨callee, post, value, rfl, args, called, callerRun⟩,
      ⟨origin, source, post, count, value, first, second, data, callerRun, firstRun, secondRun, thirdRun⟩⟩⟩

theorem separated (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached (decoderOrigin := decoderOrigin) input :=
  hashes input (HashCountReturn.separated input actual gas)

end InitECandidate.Solver.Input.CurrentStartup.RequestsEntry

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsEntry.hashes
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsEntry.separated
