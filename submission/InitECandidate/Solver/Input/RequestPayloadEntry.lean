import InitECandidate.Solver.Input.RequestOffsetValues
import InitECandidate.Solver.Input.PayloadCalleeNormal

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual normal request decoding reaches the payload callee at blob+62,
with a >=540-byte contained slice and the original copied bytes still intact. -/
theorem payload_reachable (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array total : BitVec 64) (heap : Blob.HeapInput source input pointer) (inside : 62≤input.length%2^64)
    (np : source.locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))))
    (nlen : source.locals.lookup (ofString "nlen")=some (.val (.word total)))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat)
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (payloadCode : source.code.lookup (ofString "decode_payload")=some (Payload.formals,Payload.body,.one))
    (totalUpper : total.toNat≤input.length%2^64-18) (enough : 7≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source requestBody=(some (.returned value),post)) :
    Guest.GasLimit.le32 input 18=44 ∧ 602≤input.length%2^64 ∧
    540≤Guest.GasLimit.le32 input 22-44 ∧ Guest.GasLimit.le32 input 22-44≤input.length%2^64-62 ∧
      ∃ entry bodyPost returned,
        Blob.HeapInput entry input pointer ∧
        entry.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) ∧
        entry.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44)))) ∧
        entry.code=source.code ∧ entry.eshapes=source.eshapes ∧ entry.memaddrs=source.memaddrs ∧
        entry.globals=source.globals ∧ source.clock-6≤entry.clock ∧
        evaluateHOLFiniteState entry Payload.afterGuard=(some (.returned returned),bodyPost) := by
  classical
  obtain ⟨first,valid,next,innerPost,paid,bound,nextEq,nextHeap,nextRun⟩:=offsets_normal source post input pointer array total heap inside np nlen
    arrayGlobal domain pointerAligned arrayAligned upper arrayLower arrayBefore code failCode exceptionShape (by omega) value run
  obtain ⟨rawFirst,hashLower,ordered,requestUpper⟩:=request_values input total first valid
  have hashUpper : Guest.GasLimit.le32 input 22≤input.length%2^64-18 := by omega
  have nextNp : next.locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))) := by
    rw [nextEq]
    exact (bind_lookup_other (offsetSecond source input) "o_rq" "np" _ (by decide)).trans
      ((bind_lookup_other (offsetFirst source input) "o_vh" "np" _ (by decide)).trans
        ((bind_lookup_other source "o_pl" "np" _ (by decide)).trans np))
  have nextPl : next.locals.lookup (ofString "o_pl")=some (.val (.word (requestWords input 0))) := by
    rw [nextEq]
    exact (bind_lookup_other (offsetSecond source input) "o_rq" "o_pl" _ (by decide)).trans
      ((bind_lookup_other (offsetFirst source input) "o_vh" "o_pl" _ (by decide)).trans (bind_lookup_same _ _ _))
  have nextVh : next.locals.lookup (ofString "o_vh")=some (.val (.word (requestWords input 1))) := by
    rw [nextEq]
    exact (bind_lookup_other (offsetSecond source input) "o_rq" "o_vh" _ (by decide)).trans (bind_lookup_same _ _ _)
  obtain ⟨args,sliceUpper⟩:=payload_arguments next input pointer nextNp nextPl nextVh rawFirst hashLower hashUpper inside
  have nextCode : next.code=source.code := by rw [nextEq]; rfl
  have nextShapes : next.eshapes=source.eshapes := by rw [nextEq]; rfl
  have nextClock : next.clock=source.clock-paid := by rw [nextEq]
  rw [payload_call_shape] at nextRun
  have minimum:=Payload.normal_length next innerPost payloadArguments afterPayload (pointer+62#64)
    (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44)) args (by rw [nextCode]; exact payloadCode)
    (by rw [nextCode]; exact failCode) (by rw [nextShapes]; exact exceptionShape) (by rw [nextClock]; omega) value nextRun
  have sliceNumber : (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44)).toNat=Guest.GasLimit.le32 input 22-44 := by
    have extentBound : input.length%2^64<2^64 := Nat.mod_lt _ (by decide)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [sliceNumber] at minimum
  obtain ⟨callee,called,p,n,bodyPost,returned,bodyRun⟩:=Payload.callee_normal next innerPost payloadArguments afterPayload (pointer+62#64)
    (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44)) args (by rw [nextCode]; exact payloadCode) (by rw [nextClock]; omega) value nextRun
  let entry:=callEntryStateHOLFinite next callee
  have entryHeap : Blob.HeapInput entry input pointer := Blob.HeapInput.of_fields next entry input pointer rfl rfl rfl nextHeap
  have passed:=Payload.entry_execute entry (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44)) n
    (by change next.code.lookup _=_; rw [nextCode]; exact failCode)
    (by change next.eshapes.lookup _=_; rw [nextShapes]; exact exceptionShape) (by change 1≤next.clock-1; rw [nextClock]; omega)
  simp only [sliceNumber,if_neg (show ¬Guest.GasLimit.le32 input 22-44<540 from by omega)] at passed
  have tailRun : evaluateHOLFiniteState entry Payload.afterGuard=(some (.returned returned),bodyPost) := passed.symm.trans bodyRun
  refine ⟨rawFirst,by omega,minimum,sliceUpper,entry,bodyPost,returned,entryHeap,p,n,nextCode,nextShapes,?_,?_,?_,tailRun⟩
  · change next.memaddrs=source.memaddrs
    rw [nextEq]
    rfl
  · change next.globals=source.globals
    rw [nextEq]
    rfl
  · change source.clock-6≤next.clock-1
    rw [nextClock]
    omega

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.payload_reachable
