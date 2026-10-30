import InitECandidate.Solver.Input.CurrentRlp.HeaderFields
import InitECandidate.Solver.Input.HeaderEncoding.Suffix

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding

set_option maxRecDepth 100000

theorem codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) : Codes source := by
  exact ⟨by simpa only [WideWrite.current_body] using WideWrite.original_code source.code installed,
    WideWrite.helper_codes source installed,by simpa only [WordWrite.current_body] using WordWrite.original_code source.code installed⟩

theorem tail_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) : TailCodes source := by
  constructor
  · apply Code.installed_as source.code installed .listLength
    simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
      Guest.Software.guestFn_rlp_list_header_len,RlpLength.ListHeader.formals,RlpLength.ListHeader.body,Guest.guestFn_rlp_list_header_len,
      paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
  · apply Code.installed_as source.code installed .headerLength
    simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
      Guest.Software.guestFn_rlp_header_len,RlpLength.Header.formals,RlpLength.Header.body,Guest.guestFn_rlp_header_len,
      paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
  · apply Code.installed_as source.code installed .writeList
    simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
      Guest.Software.guestFn_rlp_encode_list_header,RlpWrite.ListWrite.formals,RlpWrite.ListWrite.body,Guest.guestFn_rlp_encode_list_header,
      paramToHOL,shapeToHOL,List.map_cons,List.map_nil]

/-- All suffix outcomes obey the source allowance, at the actual physical
header and output position supplied by the preceding writer prefix. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (lower : 9≤position) (upper : position≤916)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source suffix).2.clock≤31 := by
  by_cases funded : 31≤source.clock
  · obtain ⟨target,start,encoded,paid,positive,size,bound,number,run,frame,memory,arena⟩:=suffix_execute_bounded source original header buffer position
      context (codes source installed) (tail_codes source installed) lower upper p buf funded
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at clock
    rw [run]
    change source.clock-target.clock≤31
    omega
  · omega

/-- The genuine normal suffix return has a mapped encoded output span,
length at most916, and preserves the old header/input memory and metadata. -/
theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (lower : 9≤position) (upper : position≤916)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source suffix=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤916 ∧ value=encodedPair start encoded ∧ AllocatedBytes.Arena start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧ OldMemory target.memory original buffer := by
  let padded:={source with clock:=source.clock+31}
  have paddedContext : Context padded original header buffer:=
    ⟨context.geometry,context.domain,context.oldMemory,context.headerLocal,context.heap⟩
  obtain ⟨post,start,encoded,paid,positive,size,bound,number,run,frame,memory,arena⟩:=suffix_execute_bounded padded original header buffer position
    paddedContext (codes padded installed) (tail_codes padded installed) lower upper p buf (by change 31≤source.clock+31; omega)
  have lifted:=panPropsEvaluateAddClockEq suffix source (some (.returned value)) target 31 ⟨returned,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+31}=post at endpoint
  rw [←endpoint] at frame memory
  have metadata:=congrArg MemoryMetadata.erase frame
  exact ⟨start,encoded,positive,size,answer,arena,metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.codes
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.tail_codes
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.normal

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding

/-- The final list prefix uses only its real reserved output bytes. Payload
size may exceed the old1024byte record model; the actual arithmetic derives
an exact output end at the current cursor and protects all earlier input. -/
theorem current_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0)
    (lower : buffer.toNat+9≤position) (upper : position<2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) (funded : 31≤source.clock) :
    ∃ target start encoded paid,1≤encoded ∧ encoded≤position-buffer.toNat ∧ paid≤31 ∧
      buffer.toNat≤start.toNat ∧ start.toNat≤buffer.toNat+8 ∧ start.toNat+encoded=position ∧
      evaluateHOLFiniteState source suffix=(some (.returned (encodedPair start encoded)),target) ∧
      target.clock=source.clock-paid ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query) := by
  classical
  let payload:=position-(buffer.toNat+9)
  have positionNumber : (BitVec.ofNat 64 position).toNat=position:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt upper]
  have bufferFits : buffer.toNat+18<2^64:=by have room:=reserved.upper; omega
  have bufferNine : (buffer+9#64).toNat=buffer.toNat+9:=by
    rw [BitVec.toNat_add_of_lt (by change buffer.toNat+9<2^64; omega)]
    rfl
  have payloadNumber : (BitVec.ofNat 64 payload).toNat=payload:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [payload]; omega)]
  have payloadDifference : BitVec.ofNat 64 position-(buffer+9#64)=BitVec.ofNat 64 payload:=by
    have ordered : buffer+9#64≤BitVec.ofNat 64 position:=by change (buffer+9#64).toNat≤(BitVec.ofNat 64 position).toNat; rw [bufferNine,positionNumber]; exact lower
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le ordered,positionNumber,bufferNine,payloadNumber]
  have payloadRead : eval source payloadExpression=some (.val (.word (BitVec.ofNat 64 payload))):=by
    simp [eval,payloadExpression,localVar,evalHOLExact,evalListHOLExact,toExact,p,buf,valueIsWord,valueWord,wordOpHOL,wordOp,payloadDifference]
  let sp:=bind source "payload_len" (BitVec.ofNat 64 payload)
  have payloadP : sp.locals.lookup (ofString "payload_len")=some (.val (.word (BitVec.ofNat 64 payload))):=bind_lookup_same _ _ _
  have args : evalListHOLFinite sp (h:=fun address=>Classical.propDecidable (sp.memaddrs address)) [localVar "payload_len"]=some [.val (.word (BitVec.ofNat 64 payload))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,payloadP]
  have helpers:=codes source installed
  have tails:=tail_codes source installed
  obtain ⟨hl,headerPaid,hlLower,hlUpper,headerBound,headerRun⟩:=RlpLength.ListHeader.call_execute sp (BitVec.ofNat 64 payload) "hl" [localVar "payload_len"] afterHeaderLength args
    tails.listLength tails.headerLength helpers.u256Codes.bytesCodes.beCode (by change 11≤source.clock; omega)
  let sh:=bind {sp with clock:=sp.clock-1-headerPaid} "hl" (BitVec.ofNat 64 hl)
  have bufH : sh.locals.lookup (ofString "buf")=some (.val (.word buffer)):=
    (bind_lookup_other _ "hl" "buf" _ (by decide)).trans ((bind_lookup_other _ "payload_len" "buf" _ (by decide)).trans buf)
  have hlH : sh.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))):=bind_lookup_same _ _ _
  have payloadH : sh.locals.lookup (ofString "payload_len")=some (.val (.word (BitVec.ofNat 64 payload))):=
    (bind_lookup_other _ "hl" "payload_len" _ (by decide)).trans payloadP
  let start:=buffer+BitVec.ofNat 64 (9-hl)
  have hlNumber : (BitVec.ofNat 64 hl).toNat=hl:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have offsetNumber : (BitVec.ofNat 64 (9-hl)).toNat=9-hl:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have startNumber : start.toNat=buffer.toNat+(9-hl):=by
    rw [BitVec.toNat_add_of_lt (by rw [offsetNumber]; omega),offsetNumber]
  have startDifference : (buffer+9#64)-BitVec.ofNat 64 hl=start:=by
    have ordered : BitVec.ofNat 64 hl≤buffer+9#64:=by change (BitVec.ofNat 64 hl).toNat≤(buffer+9#64).toNat; rw [hlNumber,bufferNine]; omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le ordered,bufferNine,hlNumber,startNumber]
    omega
  have startRead : eval sh startExpression=some (.val (.word start)):=by
    simp [eval,startExpression,localVar,evalHOLExact,evalListHOLExact,toExact,bufH,hlH,valueIsWord,valueWord,wordOpHOL,wordOp,startDifference]
  let ss:=bind sh "start" start
  have startS : ss.locals.lookup (ofString "start")=some (.val (.word start)):=bind_lookup_same _ _ _
  have payloadS : ss.locals.lookup (ofString "payload_len")=some (.val (.word (BitVec.ofNat 64 payload))):=
    (bind_lookup_other _ "start" "payload_len" _ (by decide)).trans payloadH
  have hlS : ss.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))):=
    (bind_lookup_other _ "start" "hl" _ (by decide)).trans hlH
  have writeArgs : evalListHOLFinite ss (h:=fun address=>Classical.propDecidable (ss.memaddrs address)) [localVar "start",localVar "payload_len"]=
      some [.val (.word start),.val (.word (BitVec.ofNat 64 payload))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,startS,payloadS]
  have arena : AllocatedBytes.Arena start 9:=AllocatedBytes.Arena.subrange buffer 18 (9-hl) 9 reserved (by omega)
  have mapped : ∀ index<9,ss.memaddrs (panByteAlignHOL (width:=64) (start+BitVec.ofNat 64 index)):=by
    intro index inside
    exact AllocatedBytes.byte_mapped ss start 9 index domain arena inside
  obtain ⟨memory,writePaid,writeBound,writeRun,memoryFrame⟩:=RlpWrite.ListWrite.call_execute ss start (BitVec.ofNat 64 payload) [localVar "start",localVar "payload_len"] writeArgs
    tails.listWriter helpers.u256Codes.bytesCodes.header helpers.u256Codes.bytesCodes.beCode helpers.u256Codes.bytesCodes.put mapped
    (by change 20≤source.clock-1-headerPaid; omega)
  let returned:={ss with memory:=memory,clock:=ss.clock-1-writePaid}
  have startR : returned.locals.lookup (ofString "start")=some (.val (.word start)):=startS
  have payloadR : returned.locals.lookup (ofString "payload_len")=some (.val (.word (BitVec.ofNat 64 payload))):=payloadS
  have hlR : returned.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))):=hlS
  have returnRun : evaluateHOLFiniteState returned returnHeader=(some (.returned (encodedPair start (payload+hl))),emptyLocalsHOLFinite returned):=by
    simp [returnHeader,encodedPair,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,startR,payloadR,hlR,valueIsWord,valueWord,
      wordOpHOL,wordOp,←BitVec.ofNat_add,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have afterRun : evaluateHOLFiniteState ss afterStart=(some (.returned (encodedPair start (payload+hl))),emptyLocalsHOLFinite returned):=by
    rw [afterStart,WitnessRadix.StateSteps.next_sequence ss returned _ _ writeRun (by change ss.clock-1-writePaid≤ss.clock; omega)]
    exact returnRun
  let ts:=restore sh "start" (emptyLocalsHOLFinite returned)
  have declared : evaluateHOLFiniteState sh afterHeaderLength=(some (.returned (encodedPair start (payload+hl))),ts):=
    ScalarScope.declare_execute sh _ "start" startExpression start afterStart _ startRead afterRun
  let th:=restore sp "hl" ts
  have calledRun : evaluateHOLFiniteState sp (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload_len"] afterHeaderLength)=
      (some (.returned (encodedPair start (payload+hl))),th):=by rw [headerRun,declared]
  let target:=restore source "payload_len" th
  let paid:=headerPaid+writePaid+2
  refine ⟨target,start,payload+hl,paid,by dsimp [payload]; omega,by dsimp [payload]; omega,by dsimp [paid]; omega,
    by rw [startNumber]; omega,by rw [startNumber]; omega,by rw [startNumber]; dsimp [payload]; omega,?_,?_,?_,?_⟩
  · rw [suffix_shape]
    exact ScalarScope.declare_execute source _ "payload_len" payloadExpression (BitVec.ofNat 64 payload) _ _ payloadRead calledRun
  · change source.clock-1-headerPaid-1-writePaid=source.clock-paid
    dsimp [paid]
    omega
  · rfl
  · intro query before
    have away:=CopyGeneral.Away.after_floor start query 9 buffer.toNat aligned (by rw [startNumber]; omega) (by rw [startNumber]; omega) before
    exact memoryFrame query (fun index inside=>(away index inside).2)

end InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.current_execute

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding

/-- Actual arbitrary-payload list suffix, including every early outcome. -/
theorem current_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0)
    (lower : buffer.toNat+9≤position) (upper : position<2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source suffix).2.clock≤31 := by
  by_cases funded : 31≤source.clock
  · obtain ⟨target,start,encoded,paid,positive,size,price,startLower,startUpper,endNumber,run,clock,metadata,memory⟩:=
      current_execute source buffer position installed domain reserved aligned lower upper p buf funded
    rw [run]
    change source.clock-target.clock≤31
    omega
  · omega

/-- A genuine normal return has its actual scalar pair, output geometry,
metadata and protected prefix at the caller's actual clock. -/
theorem current_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0)
    (lower : buffer.toNat+9≤position) (upper : position<2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source suffix=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤position-buffer.toNat ∧ buffer.toNat≤start.toNat ∧
      start.toNat≤buffer.toNat+8 ∧ start.toNat+encoded=position ∧ value=encodedPair start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query) := by
  let padded:={source with clock:=source.clock+31}
  obtain ⟨post,start,encoded,paid,positive,size,price,startLower,startUpper,endNumber,run,clock,metadata,memory⟩:=
    current_execute padded buffer position installed domain reserved aligned lower upper p buf (by change 31≤source.clock+31; omega)
  have lifted:=panPropsEvaluateAddClockEq suffix source (some (.returned value)) target 31 ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+31}=post at endpoint
  rw [←endpoint] at metadata memory
  exact ⟨start,encoded,positive,size,startLower,startUpper,endNumber,answer,metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.current_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.current_normal
