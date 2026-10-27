import InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn
import InitECandidate.Solver.Input.Witness.PrefixTrace

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessEntry
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real stateless record's request pointer store immediately precedes
the two witness declarations and their short-length guard. -/
theorem source_shape : Request.afterRequests =
    .seq (.store (Scalar.plus (localVar "si") 32) (localVar "rq")) Witness.prefixBody := by
  simp only [Request.afterRequests, Request.requestsCall, Witness.prefixBody, Payload.dropLeading,
    Request.afterHashCount, Request.hashCountCall, Request.afterPayload, Request.continuation,
    Request.requestBody, Request.prefixBody, Header.continuation, Header.afterHeader, Header.body,
    Guest.Software.guestFn_decode_stateless_input, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Scalar.plus, localVar]

structure Result (input : Guest.InputBlob) (source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) (value : ValueHOL 64) : Prop where
  prepared : current = Witness.prefixPrepared source input pointer (Guest.GasLimit.le32 input 6)
  context : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength
  heap : NormalHeapEffects.AtLeast (requestRecord.toNat + 80) current
  wp : current.locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 (2 + Guest.GasLimit.le32 input 6))))
  wlen : current.locals.lookup (ofString "wlen") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6))))
  minimum : 12 ≤ input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6
  requestCell : current.memory (statelessRecord + 32#64) = .word requestRecord
  returned : evaluateHOLFiniteState current Witness.offsetBody = (some (.returned value), post)
  endpoint : ∃ callerPost, evaluateHOLFiniteState source Witness.prefixBody = (some (.returned value), callerPost) ∧
    callerPost.clock = post.clock ∧ LocalEffects.erase callerPost = LocalEffects.erase post
  origin : ∃ caller previous previousPost counts,
    RequestCallerReturn.Result (decoderOrigin := decoderOrigin) input caller previous previousPost pointer statelessRecord record gasWord requestRecord payloadLength counts value ∧
    source = {previous with memory := WitnessRadix.StoreWord.put previous.memory (statelessRecord + 32#64) requestRecord}

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ source current post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength : Nat, ∃ value : ValueHOL 64,
      Result (decoderOrigin := decoderOrigin) input source current post pointer statelessRecord record gasWord requestRecord payloadLength value

/-- The actual returned request caller derives the witness's real12-byte
minimum, pointer and contained length. No future offset/list success is added. -/
theorem requests (input : Guest.InputBlob) (actual : RequestCallerReturn.Reached (decoderOrigin := decoderOrigin) input) : Reached (decoderOrigin := decoderOrigin) input := by
  classical
  obtain ⟨caller, source, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, counts, value, data⟩ := actual
  have context := data.context
  obtain ⟨stored, storedContext⟩ := context.stateless_store input source pointer statelessRecord record gasWord payloadLength 32
    (localVar "rq") requestRecord (by decide) (by decide) (Request.local_word source "rq" requestRecord data.rq)
  let ready := {source with memory := WitnessRadix.StoreWord.put source.memory (statelessRecord + 32#64) requestRecord}
  have callerRun := data.returned
  rw [source_shape, WitnessRadix.StateSteps.next_sequence source ready _ _ stored (Nat.le_refl _)] at callerRun
  have outer := storedContext.request.outer
  rcases Witness.prefix_trace ready post input pointer (Guest.GasLimit.le32 input 6) storedContext.image
    (by have := outer.lower; have := outer.upper; omega) outer.upper outer.p outer.len outer.wit
    (CanonicalHeader.fail_code ready.code storedContext.code) (storedContext.shapes .SszErr)
    (some (.returned value)) callerRun (by simp) with short | continued
  · obtain ⟨minimum, impossible, price⟩ := short
    cases impossible
  · obtain ⟨minimum, image, wp, wlen, inner, remaining, restored⟩ := continued
    let current := Witness.prefixPrepared ready input pointer (Guest.GasLimit.le32 input 6)
    have kept (name : String) (first : ofString "wp" ≠ ofString name) (second : ofString "wlen" ≠ ofString name) :
        current.locals.lookup (ofString name) = ready.locals.lookup (ofString name) :=
      (bind_lookup_other _ "wlen" name _ second).trans (bind_lookup_other _ "wp" name _ first)
    have request : PayloadEntry.CallerLocals input current pointer :=
      ⟨(kept "np" (by decide) (by decide)).trans storedContext.request.np,
        (kept "nlen" (by decide) (by decide)).trans storedContext.request.nlen,
        (kept "o_vh" (by decide) (by decide)).trans storedContext.request.vh,
        (kept "o_rq" (by decide) (by decide)).trans storedContext.request.rq,
        storedContext.request.valid, storedContext.request.upper, outer.preserved (by
          intro name member
          apply kept
          all_goals
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl <;> decide)⟩
    have currentContext := PayloadCallerReturn.Context.of_frame input ready current pointer statelessRecord record gasWord payloadLength
      storedContext rfl ((kept "pl" (by decide) (by decide)).trans storedContext.pl)
      ((kept "si" (by decide) (by decide)).trans storedContext.si) request
    refine ⟨ready, current, inner, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, value,
      ⟨rfl, currentContext, data.heap, wp, wlen, minimum, ?_, remaining, ⟨post, callerRun, ?_, ?_⟩, ⟨caller, source, post, counts, data, rfl⟩⟩⟩
    · change WitnessRadix.StoreWord.put source.memory (statelessRecord + 32#64) requestRecord (statelessRecord + 32#64) = _
      simp [WitnessRadix.StoreWord.put]
    · rw [restored]
      rfl
    · rw [restored]
      rfl

theorem separated (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached (decoderOrigin := decoderOrigin) input :=
  requests input (RequestCallerReturn.separated input actual gas)

end InitECandidate.Solver.Input.CurrentStartup.WitnessEntry

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessEntry.source_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessEntry.requests
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessEntry.separated
