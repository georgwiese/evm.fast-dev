import InitECandidate.Solver.Input.RlpLength.WithdrawalProgram
import InitECandidate.Solver.Input.HeapFrame

namespace InitECandidate.Solver.Input.RlpLength.Withdrawal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole actual withdrawal length computation from its44 copied bytes.
All scalar calls, payload declaration, list-header call and returns are real.
The conservative size range25..57 suffices for the global block-size resource. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+44≤input.length%2^64)
    (wd : source.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (wordCode : source.code.lookup (ofString "rlp_word_encoded_len")=some (WordSize.formals,WordSize.body,.one))
    (listCode : source.code.lookup (ofString "rlp_list_header_len")=some (ListHeader.formals,ListHeader.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 41≤source.clock) :
    ∃ target encoded paid,25≤encoded ∧ encoded≤57 ∧ paid≤41 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  have firstRead : eval source firstExpression=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)))) := by
    simpa [firstExpression] using scalar_read source input pointer start 0 heap (by omega) wd
  obtain ⟨a,pa,aLow,aHigh,paBound,callA⟩:=WordSize.call_execute source (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)) "a" [firstExpression] afterA
    (singleton_args source firstExpression _ firstRead) wordCode beCode (by omega)
  let sa:=bind {source with clock:=source.clock-1-pa} "a" (BitVec.ofNat 64 a)
  have heapA : Blob.HeapInput sa input pointer:=Blob.HeapInput.of_fields source sa input pointer rfl rfl rfl heap
  have wdA : sa.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))) :=
    (bind_lookup_other {source with clock:=source.clock-1-pa} "a" "wd" _ (by decide)).trans wd
  have secondRead : eval sa secondExpression=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+8))))) := by
    simpa [secondExpression] using scalar_read sa input pointer start 8 heapA (by omega) wdA
  obtain ⟨b,pb,bLow,bHigh,pbBound,callB⟩:=WordSize.call_execute sa (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+8))) "b" [secondExpression] afterB
    (singleton_args sa secondExpression _ secondRead) wordCode beCode (by change 10≤source.clock-1-pa; omega)
  let sb:=bind {sa with clock:=sa.clock-1-pb} "b" (BitVec.ofNat 64 b)
  have heapB : Blob.HeapInput sb input pointer:=Blob.HeapInput.of_fields sa sb input pointer rfl rfl rfl heapA
  have wdB : sb.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))) :=
    (bind_lookup_other {sa with clock:=sa.clock-1-pb} "b" "wd" _ (by decide)).trans wdA
  have thirdRead : eval sb thirdExpression=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+36))))) := by
    simpa [thirdExpression] using scalar_read sb input pointer start 36 heapB (by omega) wdB
  obtain ⟨c,pc,cLow,cHigh,pcBound,callC⟩:=WordSize.call_execute sb (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+36))) "c" [thirdExpression] afterC
    (singleton_args sb thirdExpression _ thirdRead) wordCode beCode (by change 10≤source.clock-1-pa-1-pb; omega)
  let sc:=bind {sb with clock:=sb.clock-1-pc} "c" (BitVec.ofNat 64 c)
  let payload:=a+b+21+c
  have aLocal : sc.locals.lookup (ofString "a")=some (.val (.word (BitVec.ofNat 64 a))) :=
    (bind_lookup_other _ "c" "a" _ (by decide)).trans ((bind_lookup_other _ "b" "a" _ (by decide)).trans (bind_lookup_same _ _ _))
  have bLocal : sc.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 b))) :=
    (bind_lookup_other _ "c" "b" _ (by decide)).trans (bind_lookup_same _ _ _)
  have cLocal : sc.locals.lookup (ofString "c")=some (.val (.word (BitVec.ofNat 64 c))):=bind_lookup_same _ _ _
  have payloadRead : eval sc payloadExpression=some (.val (.word (BitVec.ofNat 64 payload))) := by
    simp [eval,payloadExpression,localVar,evalHOLExact,evalListHOLExact,toExact,aLocal,bLocal,cLocal,valueIsWord,valueWord,wordOpHOL,wordOp,
      payload,←BitVec.ofNat_add,Nat.add_assoc]
  let sp:=bind sc "payload" (BitVec.ofNat 64 payload)
  have payloadLocal : sp.locals.lookup (ofString "payload")=some (.val (.word (BitVec.ofNat 64 payload))):=bind_lookup_same _ _ _
  have payloadArgs : evalListHOLFinite sp (h:=fun address=>Classical.propDecidable (sp.memaddrs address)) [localVar "payload"]=some [.val (.word (BitVec.ofNat 64 payload))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,payloadLocal]
  obtain ⟨hl,ph,hLow,hHigh,phBound,callH⟩:=ListHeader.call_execute sp (BitVec.ofNat 64 payload) "hl" [localVar "payload"] returnLength
    payloadArgs listCode headerCode beCode (by change 11≤source.clock-1-pa-1-pb-1-pc; omega)
  let sh:=bind {sp with clock:=sp.clock-1-ph} "hl" (BitVec.ofNat 64 hl)
  have hlLocal : sh.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))):=bind_lookup_same _ _ _
  have savedPayload : sh.locals.lookup (ofString "payload")=some (.val (.word (BitVec.ofNat 64 payload))) :=
    (bind_lookup_other _ "hl" "payload" _ (by decide)).trans payloadLocal
  have returnRun : evaluateHOLFiniteState sh returnLength=(some (.returned (.val (.word (BitVec.ofNat 64 (payload+hl))))),emptyLocalsHOLFinite sh) := by
    simp [returnLength,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,savedPayload,hlLocal,valueIsWord,valueWord,
      wordOpHOL,wordOp,←BitVec.ofNat_add,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  let th:=restore sp "hl" (emptyLocalsHOLFinite sh)
  have headerRun : evaluateHOLFiniteState sp payloadTail=(some (.returned (.val (.word (BitVec.ofNat 64 (payload+hl))))),th) := by
    change evaluateHOLFiniteState sp (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload"] returnLength)=_
    rw [callH,returnRun]
  let tp:=restore sc "payload" th
  have payloadRun : evaluateHOLFiniteState sc afterC=(some (.returned (.val (.word (BitVec.ofNat 64 (payload+hl))))),tp) :=
    ScalarScope.declare_execute sc th "payload" payloadExpression (BitVec.ofNat 64 payload) payloadTail _ payloadRead headerRun
  let tc:=restore sb "c" tp
  have cRun : evaluateHOLFiniteState sb afterB=(some (.returned (.val (.word (BitVec.ofNat 64 (payload+hl))))),tc) := by
    rw [afterB,callC,payloadRun]
  let tb:=restore sa "b" tc
  have bRun : evaluateHOLFiniteState sa afterA=(some (.returned (.val (.word (BitVec.ofNat 64 (payload+hl))))),tb) := by
    rw [afterA,callB,cRun]
  let target:=restore source "a" tb
  let paid:=pa+pb+pc+ph+4
  refine ⟨target,payload+hl,paid,by dsimp [payload]; omega,by dsimp [payload]; omega,by dsimp [paid]; omega,?_,?_⟩
  · rw [body_shape,callA,bRun]
  · have subtraction : source.clock-1-pa-1-pb-1-pc-1-ph=source.clock-paid := by dsimp [paid]; omega
    change emptyLocalsHOLFinite {source with clock:=source.clock-1-pa-1-pb-1-pc-1-ph}=emptyLocalsHOLFinite {source with clock:=source.clock-paid}
    rw [subtraction]

end InitECandidate.Solver.Input.RlpLength.Withdrawal

#print axioms InitECandidate.Solver.Input.RlpLength.Withdrawal.execute
