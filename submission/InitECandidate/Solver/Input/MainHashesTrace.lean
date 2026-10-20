import InitECandidate.Solver.Input.MainPayloadStore
import InitECandidate.Solver.Input.FixedList.CallerTrace

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def hashesArguments : List (ExpHOL 64) := [.op .sub [localVar "o_rq",localVar "o_vh"],.const 32#64,.const 9223372036854775807#64]
def afterHashes : ProgHOL 64 := match hashesCall with | .decCall _ _ _ _ rest => rest | _ => .skip

theorem hashes_call_shape : hashesCall = .decCall (ofString "nvh") .one (ofString "ssz_fixed_list_count") hashesArguments afterHashes := by
  simp only [hashesCall,afterHashes,afterPayload,continuation,requestBody,prefixBody,Header.continuation,Header.afterHeader,Header.body,
    Guest.guestFn_decode_stateless_input,progToHOL,shapeToHOL,Option.map_none,hashesArguments,localVar,expToHOL,List.map_cons,List.map_nil]

end InitECandidate.Solver.Input.Request

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual original blob-hash list count after payload resumption, including
both real fixed-list rejection outcomes. Its length and count come from the
validated request offsets; the later continuation need not succeed. -/
theorem hashes_trace (input : Guest.InputBlob) (source caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actualCaller : DecoderCall.PayloadCaller input source caller)
    (returned : Returned input caller current) (layout : DecoderCall.RequestLayout input)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState current Request.hashesCall = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 30#64 ∨ error = 31#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ current.clock - post.clock ≤ 67) ∨
    (∃ next innerPost count,next.locals = current.locals.update (ofString "nvh",.val (.word count)) ∧
      count.toNat = (Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32 ∧
      (Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) % 32 = 0 ∧
      next.clock ≤ current.clock ∧ current.clock - next.clock ≤ 67 ∧ caller.clock - next.clock ≤ (input.length % 2^64) / 4 + 143 ∧
      UDivMod.frozen next = UDivMod.frozen current ∧ Blob.HeapInput next input inputPointer ∧
      next.memory (cursor input + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      next.memory (cursor input + 56#64) = .word (BitVec.ofNat 64 (Payload.withdrawalCount input)) ∧
      evaluateHOLFiniteState next Request.afterHashes = (result,innerPost) ∧ post = restore current "nvh" innerPost) := by
  have other (key : String) (different : ofString "pl" ≠ ofString key) : current.locals.lookup (ofString key) = caller.locals.lookup (ofString key) := by
    rw [returned.locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,different]
  have rq := (other "o_rq" (by decide)).trans actualCaller.requestsOffset
  have vh := (other "o_vh" (by decide)).trans actualCaller.hashesOffset
  let span := BitVec.ofNat 64 (Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22)
  have offsetSmall := HostGas.le32_lt input 22
  rw [HostGas.le32_eq input 22 (by decide)] at offsetSmall
  have subtract : BitVec.ofNat 64 (Guest.GasLimit.le32 input 58) - BitVec.ofNat 64 (Guest.GasLimit.le32 input 22) = span :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) layout.offsetsOrdered
  have args : evalListHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) Request.hashesArguments =
      some (FixedList.values span 32#64 9223372036854775807#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,Request.hashesArguments,localVar,rq,vh,Request.requestWords,
      FixedList.values,valueIsWord,valueWord,wordOpHOL,wordOp,subtract]
  have installed : OriginalCode.Installed current.code := returned.code.symm ▸ (actualCaller.frame.code.symm ▸ environment.code)
  have exceptionShape : current.eshapes.lookup (ofString "SszErr") = some .one := by rw [returned.exceptions,actualCaller.frame.exceptions]; exact environment.shapes .SszErr
  rw [Request.hashes_call_shape] at run
  rcases FixedList.caller_trace current post span 32#64 9223372036854775807#64 (by decide)
    (DecoderRuntime.division_code current.code installed) (DecoderCall.original_fail_code current.code installed) exceptionShape (DecoderRuntime.fixed_list_code current.code installed)
    "nvh" Request.hashesArguments Request.afterHashes args result run notTimeout with rejected | normal
  · exact Or.inl rejected
  · obtain ⟨next,innerPost,count,locals,countBound,forward,cost,frame,remaining,restored,arithmetic⟩ := normal
    have memory : next.memory = current.memory := by
      have projected := congrArg PanSemStateFiniteExact.memory frame
      exact projected
    have domain : next.memaddrs = current.memaddrs := by
      have projected := congrArg PanSemStateFiniteExact.memaddrs frame
      exact projected
    have endian : next.be = current.be := by
      have projected := congrArg PanSemStateFiniteExact.be frame
      exact projected
    have spanNat : span.toNat = Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22 := by
      have small := HostGas.le32_lt input 58
      rw [HostGas.le32_eq input 58 (by decide)] at small
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    obtain ⟨countNat,remainder⟩ := arithmetic (by decide)
    rw [spanNat] at countNat remainder
    have before := returned.forward
    have previousCost := returned.cost
    exact Or.inr ⟨next,innerPost,count,locals,countNat,remainder,forward,cost,by omega,frame,
      Blob.HeapInput.of_fields current next input inputPointer memory.symm domain.symm endian.symm returned.bytes,
      by rw [memory]; exact returned.gasCell,by rw [memory]; exact returned.countCell,remaining,restored⟩

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Request.hashes_call_shape
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.hashes_trace
