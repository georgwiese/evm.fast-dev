import InitECandidate.Solver.Input.HeaderEncoding.SuffixArithmetic

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual payload subtraction, list-length call, start subtraction, list
writer, tuple return and all scopes. Both subtractions have natural meanings. -/
theorem suffix_execute_bounded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (codes : Codes source) (tailCodes : TailCodes source)
    (lower : 9≤position) (upper : position≤916)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) (enough : 31≤source.clock) :
    ∃ target start encoded paid,1≤encoded ∧ encoded≤916 ∧ paid≤31 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source suffix=(some (.returned (encodedPair start encoded)),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      OldMemory target.memory original buffer ∧ WitnessRadix.AllocatedBytes.Arena start encoded := by
  classical
  let payload:=position-9
  have payloadRead : eval source payloadExpression=some (.val (.word (BitVec.ofNat 64 payload))) := by
    simp [eval,payloadExpression,localVar,evalHOLExact,evalListHOLExact,toExact,p,buf,valueIsWord,valueWord,wordOpHOL,wordOp,
      payload_difference header buffer context.geometry position lower upper,payload]
  let sp:=bind source "payload_len" (BitVec.ofNat 64 payload)
  have payloadP : sp.locals.lookup (ofString "payload_len")=some (.val (.word (BitVec.ofNat 64 payload))):=bind_lookup_same _ _ _
  have args : evalListHOLFinite sp (h:=fun address=>Classical.propDecidable (sp.memaddrs address)) [localVar "payload_len"]=some [.val (.word (BitVec.ofNat 64 payload))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,payloadP]
  obtain ⟨hl,headerPaid,hlLower,hlUpper,headerBound,headerRun⟩:=RlpLength.ListHeader.call_execute sp (BitVec.ofNat 64 payload) "hl" [localVar "payload_len"] afterHeaderLength args
    tailCodes.listLength tailCodes.headerLength codes.u256Codes.bytesCodes.beCode (by change 11≤source.clock; omega)
  let sh:=bind {sp with clock:=sp.clock-1-headerPaid} "hl" (BitVec.ofNat 64 hl)
  have bufH : sh.locals.lookup (ofString "buf")=some (.val (.word buffer)):=
    (bind_lookup_other _ "hl" "buf" _ (by decide)).trans ((bind_lookup_other _ "payload_len" "buf" _ (by decide)).trans buf)
  have hlH : sh.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))):=bind_lookup_same _ _ _
  have payloadH : sh.locals.lookup (ofString "payload_len")=some (.val (.word (BitVec.ofNat 64 payload))):=
    (bind_lookup_other _ "hl" "payload_len" _ (by decide)).trans payloadP
  let start:=address buffer (9-hl)
  have startRead : eval sh startExpression=some (.val (.word start)) := by
    simp [eval,startExpression,localVar,evalHOLExact,evalListHOLExact,toExact,bufH,hlH,valueIsWord,valueWord,wordOpHOL,wordOp,
      start_difference header buffer context.geometry hl hlLower hlUpper,start]
  let ss:=bind sh "start" start
  have startS : ss.locals.lookup (ofString "start")=some (.val (.word start)):=bind_lookup_same _ _ _
  have payloadS : ss.locals.lookup (ofString "payload_len")=some (.val (.word (BitVec.ofNat 64 payload))):=
    (bind_lookup_other _ "start" "payload_len" _ (by decide)).trans payloadH
  have hlS : ss.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))):=
    (bind_lookup_other _ "start" "hl" _ (by decide)).trans hlH
  have writeArgs : evalListHOLFinite ss (h:=fun address=>Classical.propDecidable (ss.memaddrs address)) [localVar "start",localVar "payload_len"]=
      some [.val (.word start),.val (.word (BitVec.ofNat 64 payload))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,startS,payloadS]
  have arena:=context.geometry.position_arena header buffer (9-hl) 9 (by omega)
  have mapped : ∀ index<9,ss.memaddrs (panByteAlignHOL (width:=64) (start+BitVec.ofNat 64 index)) := by
    intro index small
    exact WitnessRadix.AllocatedBytes.byte_mapped ss start 9 index context.domain arena small
  obtain ⟨memory,writePaid,writeBound,writeRun,memoryFrame⟩:=RlpWrite.ListWrite.call_execute ss start (BitVec.ofNat 64 payload) [localVar "start",localVar "payload_len"] writeArgs
    tailCodes.listWriter codes.u256Codes.bytesCodes.header codes.u256Codes.bytesCodes.beCode codes.u256Codes.bytesCodes.put mapped
      (by change 20≤source.clock-1-headerPaid; omega)
  let returned:={ss with memory:=memory,clock:=ss.clock-1-writePaid}
  have startR : returned.locals.lookup (ofString "start")=some (.val (.word start)):=startS
  have payloadR : returned.locals.lookup (ofString "payload_len")=some (.val (.word (BitVec.ofNat 64 payload))):=payloadS
  have hlR : returned.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))):=hlS
  have returnRun : evaluateHOLFiniteState returned returnHeader=(some (.returned (encodedPair start (payload+hl))),emptyLocalsHOLFinite returned) := by
    simp [returnHeader,encodedPair,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,startR,payloadR,hlR,valueIsWord,valueWord,
      wordOpHOL,wordOp,←BitVec.ofNat_add,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have writeAndReturn : evaluateHOLFiniteState ss afterStart=(some (.returned (encodedPair start (payload+hl))),emptyLocalsHOLFinite returned) := by
    rw [afterStart,WitnessRadix.StateSteps.next_sequence ss returned _ _ writeRun (by change ss.clock-1-writePaid≤ss.clock; omega)]
    exact returnRun
  let ts:=restore sh "start" (emptyLocalsHOLFinite returned)
  have startDeclared : evaluateHOLFiniteState sh afterHeaderLength=(some (.returned (encodedPair start (payload+hl))),ts) :=
    ScalarScope.declare_execute sh _ "start" startExpression start afterStart _ startRead writeAndReturn
  let th:=restore sp "hl" ts
  have calledRun : evaluateHOLFiniteState sp (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload_len"] afterHeaderLength)=
      (some (.returned (encodedPair start (payload+hl))),th) := by
    rw [headerRun,startDeclared]
  let target:=restore source "payload_len" th
  let paid:=headerPaid+writePaid+2
  refine ⟨target,start,payload+hl,paid,by dsimp [payload]; omega,by dsimp [payload]; omega,by dsimp [paid]; omega,?_,?_,?_,?_,?_⟩
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [payload]; omega)]
  · rw [suffix_shape]
    exact ScalarScope.declare_execute source _ "payload_len" payloadExpression (BitVec.ofNat 64 payload) _ _ payloadRead calledRun
  · have subtract : source.clock-1-headerPaid-1-writePaid=source.clock-paid := by dsimp [paid]; omega
    change emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1-headerPaid-1-writePaid}=
      emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-paid}
    rw [subtract]
  · intro query before
    have number:=context.geometry.position_number header buffer (9-hl) (by omega)
    have away:=before_away start query 9 buffer.toNat arena (by dsimp [start]; omega) context.geometry.bufferAligned before
    exact (memoryFrame query (by intro index small; exact (away index small).2)).trans (context.oldMemory query before)

  · exact context.geometry.position_arena header buffer (9-hl) (payload+hl) (by dsimp [payload]; omega)

/-- Compatibility projection of the bounded physical-output contract. -/
theorem suffix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (codes : Codes source) (tailCodes : TailCodes source)
    (lower : 9≤position) (upper : position≤916)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) (enough : 31≤source.clock) :
    ∃ target start encoded paid,1≤encoded ∧ encoded≤916 ∧ paid≤31 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source suffix=(some (.returned (encodedPair start encoded)),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      OldMemory target.memory original buffer := by
  obtain ⟨target,start,encoded,paid,positive,bound,price,number,run,frame,memory,arena⟩:=
    suffix_execute_bounded source original header buffer position context codes tailCodes lower upper p buf enough
  exact ⟨target,start,encoded,paid,positive,bound,price,number,run,frame,memory⟩

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.suffix_execute

#print axioms InitECandidate.Solver.Input.HeaderEncoding.suffix_execute_bounded
