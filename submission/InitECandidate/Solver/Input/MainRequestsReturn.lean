import InitECandidate.Solver.Input.MainRequestsBody
import InitECandidate.Solver.Input.Requests.PassingEntry
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

structure RequestsReturned (input : Guest.InputBlob) (source caller current : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64) : Prop where
  locals : current.locals = caller.locals.update (ofString "rq",.val (.word (PayloadPrefix.finalCursor input)))
  bytes : Blob.HeapInput current input inputPointer
  control : BackingLayout.control current = BackingLayout.control (PersistentAlloc.post caller (PayloadPrefix.finalCursor input) 80#64)
  code : current.code = caller.code
  domain : current.memaddrs = caller.memaddrs
  exceptions : current.eshapes = caller.eshapes
  heap : current.globals.lookup (ofString "heap_ptr") = some (.val (.word (PersistentAlloc.rounded (PayloadPrefix.finalCursor input) 80#64)))
  gasCell : current.memory (PayloadPrefix.cursor input + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474))
  countCell : current.memory (PayloadPrefix.cursor input + 56#64) = .word (BitVec.ofNat 64 (Payload.withdrawalCount input))
  roots : current.locals.lookup (ofString "p") = some (.val (.word (inputPointer + 2#64))) ∧
    current.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) ∧
    current.locals.lookup (ofString "o_wit") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6))))
  si : current.locals.lookup (ofString "si") = some (.val (.word (RequestPrefix.cursor input)))
  globals : ∀ key,key ≠ ofString "heap_ptr" → current.globals.lookup key = source.globals.lookup key
  layout : Requests.Layout (Requests.offsetWord input (requestStart input)) (BitVec.ofNat 64 (requestLength input))
  image : Requests.Image current (inputPointer + BitVec.ofNat 64 (requestStart input)) (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) counts
  transactions : Payload.transactionCount input ≤ (input.length % 2^64) / 4
  forward : current.clock ≤ caller.clock
  cost : caller.clock - current.clock ≤ 349
  aggregate : source.clock - current.clock ≤ (input.length % 2^64) / 4 + 502
  earlier : ∀ query,inputPointer.toNat≤query.toNat → query.toNat<(PayloadPrefix.finalCursor input).toNat → query≠byteAddress (RequestPrefix.cursor input) 32 → current.memory query=caller.memory query

/-- Complete actual original request call: every parser rejection stops the
same execution, or the real request pointer enters the unchanged witness
continuation with its saved outer locals and real payload fields intact. -/
theorem requests_return_trace (input : Guest.InputBlob) (source caller post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (actual : RequestCaller input source caller) (layout : RequestLayout input)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState caller Request.requestsCall = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 60#64 ∨ error = 10#64 ∨ error = 11#64 ∨ error = 12#64 ∨ error = 30#64 ∨ error = 31#64) ∧
      result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ caller.clock - post.clock ≤ 349 ∧ source.clock - post.clock ≤ (input.length % 2^64) / 4 + 502) ∨
    (∃ current final counts,RequestsReturned input source caller current counts ∧ evaluateHOLFiniteState current Request.afterRequests = (result,final) ∧ post = restore caller "rq" final) := by
  obtain ⟨inside,outcome⟩ := requests_call_trace input source caller post environment actual layout result run notTimeout
  rcases outcome with rejected | normal
  · obtain ⟨minimum,same,cost⟩ := rejected
    have forward := evaluateHOLFiniteState_clock_le caller Request.requestsCall
    rw [run] at forward
    change post.clock ≤ caller.clock at forward
    have before := actual.forward
    have prefixCost := actual.cost
    exact Or.inl ⟨60#64,Or.inl rfl,same,by omega,by omega⟩
  · obtain ⟨minimum,callee,bodyResult,bodyPost,called,entry,funded,bodyNotTimeout,bodyRun⟩ := normal
    have args := (requests_arguments input source caller actual layout).1
    have lengthNumber : (BitVec.ofNat 64 (requestLength input)).toNat = requestLength input := by
      have small : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have passing := Requests.passing_entry (callEntryStateHOLFinite caller callee) (BitVec.ofNat 64 (requestLength input)) entry.length (by rw [lengthNumber]; exact minimum)
    have fullBody := passing.trans bodyRun
    rcases requests_body input source (callEntryStateHOLFinite caller callee) bodyPost environment entry bounded inside minimum bodyResult bodyRun bodyNotTimeout with rejected | normal
    · obtain ⟨error,allowed,same,cost,aggregate⟩ := rejected
      have realBody : evaluateHOLFiniteState (callEntryStateHOLFinite caller callee) Requests.body = (some (.exception (ofString "SszErr") (.val (.word error))),bodyPost) := by rw [fullBody,same]
      have observed := run
      rw [Request.requests_call_shape,evaluateHOLFiniteState_decCall_fixClockRewrite] at observed
      simp only [args,called,if_neg (show caller.clock ≠ 0 by omega)] at observed
      rw [realBody] at observed
      have endpoint : post.clock = bodyPost.clock := by have h := congrArg (fun output => output.2.clock) observed; exact h.symm
      have bodyForward := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite caller callee) Requests.afterGuard
      rw [bodyRun] at bodyForward
      change bodyPost.clock ≤ caller.clock - 1 at bodyForward
      change caller.clock - 1 - bodyPost.clock ≤ 348 at cost
      exact Or.inl ⟨error,Or.inr allowed,(congrArg Prod.fst observed).symm,by rw [endpoint]; omega,by rw [endpoint]; exact aggregate⟩
    · obtain ⟨same,counts,decoded⟩ := normal
      have realBody : evaluateHOLFiniteState (callEntryStateHOLFinite caller callee) Requests.body = (some (.returned (.val (.word (PayloadPrefix.finalCursor input)))),bodyPost) := by rw [fullBody,same]
      have shapePass : (shapeEqHOL (shapeOfHOLExact (.val (.word (PayloadPrefix.finalCursor input)))) .one && shapeEqHOL (shapeOfHOLExact (.val (.word (PayloadPrefix.finalCursor input)))) .one) = true := by simp [shapeOfHOLExact,shapeEqHOL]
      have resumed := CallNormal.return_execute caller bodyPost "rq" .one (ofString "decode_requests") Request.requestsArguments
        (Requests.values (inputPointer + BitVec.ofNat 64 (requestStart input)) (BitVec.ofNat 64 (requestLength input))) Requests.body Request.afterRequests callee .one
        (.val (.word (PayloadPrefix.finalCursor input))) args called funded realBody shapePass
      have original := run
      rw [Request.requests_call_shape] at original
      have continued := resumed.symm.trans original
      let current := CallNormal.continuationEntry caller bodyPost "rq" (.val (.word (PayloadPrefix.finalCursor input)))
      let final := (evaluateHOLFiniteState current Request.afterRequests).2
      have observed := congrArg Prod.fst continued
      have endpoint : post = restore caller "rq" final := (congrArg Prod.snd continued).symm
      have locals : current.locals = caller.locals.update (ofString "rq",.val (.word (PayloadPrefix.finalCursor input))) := rfl
      have saved (key : String) (different : ofString "rq" ≠ ofString key) : current.locals.lookup (ofString key) = caller.locals.lookup (ofString key) := by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,different]
      have bytes := Blob.HeapInput.of_fields bodyPost current input inputPointer rfl rfl rfl decoded.bytes
      have control : BackingLayout.control current = BackingLayout.control (PersistentAlloc.post caller (PayloadPrefix.finalCursor input) 80#64) := decoded.control
      have fields := evaluation_fields (callEntryStateHOLFinite caller callee) bodyPost Requests.afterGuard bodyResult bodyRun
      have globals : current.globals = caller.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded (PayloadPrefix.finalCursor input) 80#64))) := by
        have h := congrArg PanSemStateFiniteExact.globals control
        exact h
      have otherGlobals (key : MlS) (different : key ≠ ofString "heap_ptr") : current.globals.lookup key = source.globals.lookup key := by
        rw [globals]
        simpa [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different] using actual.globals key different
      have bodyCost : caller.clock - 1 - current.clock ≤ 348 := decoded.bodyCost
      have forward : current.clock ≤ caller.clock - 1 := decoded.forward
      have image : Requests.Image current (inputPointer + BitVec.ofNat 64 (requestStart input)) (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) counts := ⟨decoded.image.cells,decoded.image.arithmetic⟩
      have metadata : RequestsReturned input source caller current counts := ⟨locals,bytes,control,fields.2.2.2,fields.1,fields.2.2.1,decoded.heap,
        (decoded.payload 88 (by decide)).trans actual.gasCell,(decoded.payload 56 (by decide)).trans actual.countCell,
        ⟨(saved "p" (by decide)).trans actual.roots.1,(saved "len" (by decide)).trans actual.roots.2.1,(saved "o_wit" (by decide)).trans actual.roots.2.2⟩,
        (saved "si" (by decide)).trans actual.si,otherGlobals,decoded.layout,image,actual.transactions,by omega,by omega,decoded.cost,by intro query lower before different; exact decoded.earlier query lower before⟩
      exact Or.inr ⟨current,final,counts,metadata,Prod.ext observed rfl,endpoint⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.requests_return_trace
