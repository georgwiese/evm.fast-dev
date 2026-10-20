import InitECandidate.Solver.Input.MainHashFields
import InitECandidate.Solver.Input.Requests.Entry

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def requestsArguments : List (ExpHOL 64) := [.op .add [localVar "np",localVar "o_rq"],.op .sub [localVar "nlen",localVar "o_rq"]]
def afterRequests : ProgHOL 64 := match requestsCall with | .decCall _ _ _ _ rest => rest | _ => .skip

theorem requests_call_shape : requestsCall = .decCall (ofString "rq") .one (ofString "decode_requests") requestsArguments afterRequests := by
  simp only [requestsCall,afterRequests,afterHashes,hashesCall,afterPayload,continuation,requestBody,prefixBody,Header.continuation,Header.afterHeader,Header.body,
    Guest.guestFn_decode_stateless_input,progToHOL,shapeToHOL,Option.map_none,requestsArguments,localVar,expToHOL,List.map_cons,List.map_nil]

end InitECandidate.Solver.Input.Request

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def requestStart (input : Guest.InputBlob) := 18 + Guest.GasLimit.le32 input 58
def requestLength (input : Guest.InputBlob) := Guest.GasLimit.le32 input 6 - 16 - Guest.GasLimit.le32 input 58

structure RequestsEntry (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  bytes : Blob.HeapInput current input inputPointer
  code : current.code = source.code
  exceptions : current.eshapes = source.eshapes
  domain : current.memaddrs = source.memaddrs
  heap : current.globals.lookup (ofString "heap_ptr") = some (.val (.word (PayloadPrefix.finalCursor input)))
  offsets : current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64))
  pointer : current.locals.lookup (ofString "p") = some (.val (.word (inputPointer + BitVec.ofNat 64 (requestStart input))))
  length : current.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (requestLength input))))
  transactions : Payload.transactionCount input ≤ (input.length % 2^64) / 4
  forward : current.clock ≤ source.clock
  cost : source.clock - current.clock ≤ (input.length % 2^64) / 4 + 154

/-- Derive the original request slice and ABI from the actual main decoder
caller. The slice is contained in the same copied input extent. -/
theorem requests_arguments (input : Guest.InputBlob) (source caller : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : RequestCaller input source caller) (layout : RequestLayout input) :
    evalListHOLFinite caller (h := fun address => Classical.propDecidable (caller.memaddrs address)) Request.requestsArguments =
      some (Requests.values (inputPointer + BitVec.ofNat 64 (requestStart input)) (BitVec.ofNat 64 (requestLength input))) ∧
      requestStart input + requestLength input ≤ input.length % 2^64 := by
  have small := HostGas.le32_lt input 58
  rw [HostGas.le32_eq input 58 (by decide)] at small
  have subtraction : BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16) - BitVec.ofNat 64 (Guest.GasLimit.le32 input 58) = BitVec.ofNat 64 (requestLength input) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) layout.hashesUpper
  have bound := layout.requestUpper
  have last := layout.hashesUpper
  have extent := layout.extent
  refine ⟨?_,by dsimp only [requestStart,requestLength]; omega⟩
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,Request.requestsArguments,Request.requestWords,Requests.values,
    WitnessRadix.QueryBranch.localVar,actual.np,actual.length,actual.requestsOffset,valueIsWord,valueWord,wordOpHOL,wordOp,
    BitVec.add_assoc,BitVec.ofNat_add,requestStart,subtraction]

/-- The reached original request caller either raises its real short-slice
error within two ticks, or reaches the genuine after-guard callee body with
all code/heap/workspace/bytes premises derived. Future success is not assumed. -/
theorem requests_call_trace (input : Guest.InputBlob) (source caller post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (actual : RequestCaller input source caller) (layout : RequestLayout input)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState caller Request.requestsCall = (result,post)) (notTimeout : result ≠ some .timeOut) :
    requestStart input + requestLength input ≤ input.length % 2^64 ∧
      ((requestLength input < 20 ∧ result = some (.exception (ofString "SszErr") (.val (.word 60#64))) ∧ caller.clock - post.clock ≤ 2) ∨
        (20 ≤ requestLength input ∧ ∃ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (bodyResult : Option (PanSemResultExact 64)) (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory),
          lookupCodeHOLFinite caller.code.lookup (ofString "decode_requests") (Requests.values (inputPointer + BitVec.ofNat 64 (requestStart input)) (BitVec.ofNat 64 (requestLength input))) = some (Requests.body,callee,.one) ∧
          RequestsEntry input source (callEntryStateHOLFinite caller callee) ∧ 1 ≤ caller.clock ∧ bodyResult ≠ some .timeOut ∧
          evaluateHOLFiniteState (callEntryStateHOLFinite caller callee) Requests.afterGuard = (bodyResult,bodyPost))) := by
  obtain ⟨args,inside⟩ := requests_arguments input source caller actual layout
  have lengthNumber : (BitVec.ofNat 64 (requestLength input)).toNat = requestLength input := by
    have totalSmall : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have installed : OriginalCode.Installed caller.code := actual.code.symm ▸ environment.code
  rw [Request.requests_call_shape] at run
  rcases Requests.call_trace caller post Request.requestsArguments Request.afterRequests (inputPointer + BitVec.ofNat 64 (requestStart input)) (BitVec.ofNat 64 (requestLength input))
    args (Requests.original_code caller.code installed) (original_fail_code caller.code installed) (by rw [actual.exceptions]; exact environment.shapes .SszErr)
    result run notTimeout with rejected | normal
  · rw [lengthNumber] at rejected
    exact ⟨inside,Or.inl rejected⟩
  · obtain ⟨minimum,callee,bodyResult,bodyPost,called,p,n,funded,bodyNotTimeout,bodyRun⟩ := normal
    rw [lengthNumber] at minimum
    have bytes := Blob.HeapInput.of_fields caller (callEntryStateHOLFinite caller callee) input inputPointer rfl rfl rfl actual.bytes
    have earlier := actual.forward
    have cost := actual.cost
    have metadata : RequestsEntry input source (callEntryStateHOLFinite caller callee) := ⟨bytes,actual.code,actual.exceptions,actual.domain,actual.heap,actual.offsets,p,n,actual.transactions,
      by change caller.clock - 1 ≤ source.clock; omega,by change source.clock - (caller.clock - 1) ≤ _; omega⟩
    exact ⟨inside,Or.inr ⟨minimum,callee,bodyResult,bodyPost,called,metadata,funded,bodyNotTimeout,bodyRun⟩⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Request.requests_call_shape
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.requests_arguments
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.requests_call_trace
