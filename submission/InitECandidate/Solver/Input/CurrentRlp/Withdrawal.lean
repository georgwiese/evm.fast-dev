import InitECandidate.Solver.Input.CurrentRlp.BytesWrite
import InitECandidate.Solver.Input.NoReturnAtoms
import InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix

namespace InitECandidate.Solver.Input.CurrentRlp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual short header branch returns exactly one byte. The sharper
normal size is needed for the unchanged 64-byte withdrawal buffer. -/
theorem HeaderWrite.short_body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (small : word.toNat≤55) (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word word))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source HeaderWrite.body=(some (.returned value),target)) : value=.val (.word 1#64) := by
  have read : eval source RlpWrite.HeaderWrite.condition=some (.val (.word 1#64)):=by
    simp [eval,RlpWrite.HeaderWrite.condition,evalHOLExact,toExact,localVar,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,small]
  have guard : evaluateHOLFiniteState source (.ite RlpWrite.HeaderWrite.condition (RlpWrite.shortForm RlpWrite.HeaderWrite.shortTag) .skip)=
      evaluateHOLFiniteState source (RlpWrite.shortForm RlpWrite.HeaderWrite.shortTag):=by
    rw [evaluateHOLFiniteState_ite]
    simp only [eval] at read
    rw [read]
    simp
  have selected : evaluateHOLFiniteState source HeaderWrite.body=evaluateHOLFiniteState source (RlpWrite.shortForm RlpWrite.HeaderWrite.shortTag):=by
    rw [HeaderWrite.current_body,RlpWrite.HeaderWrite.body_shape,evaluateHOLFiniteState_seq_line780,guard]
    have stops:=HeaderWrite.short_stops source RlpWrite.HeaderWrite.shortTag
    generalize computed : evaluateHOLFiniteState source (RlpWrite.shortForm RlpWrite.HeaderWrite.shortTag)=output at stops ⊢
    obtain ⟨result,current⟩:=output
    cases result with
    | none=>exact (stops rfl).elim
    | some result=>rfl
  exact (HeaderWrite.short_normal source target dst _ d value (selected.symm.trans normal)).1

/-- The address inside a withdrawal is encoded as exactly 21 bytes.
This follows from the actual 20-byte branch and its real helper return,
independently of the address bytes and of future writer success. -/
theorem BytesWrite.twenty_normal_value (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word 20#64)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source BytesWrite.body=(some (.returned value),target)) :
    value=.val (.word 21#64) := by
  have read : eval source RlpWrite.BytesWrite.oneTest=some (.val (.word 0#64)):=by
    simp [eval,RlpWrite.BytesWrite.oneTest,localVar,evalHOLExact,toExact,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have guard : evaluateHOLFiniteState source RlpWrite.BytesWrite.firstGuard=(none,source):=by
    rw [RlpWrite.BytesWrite.firstGuard,evaluateHOLFiniteState_ite]
    simp only [eval] at read
    rw [read]
    simp [evaluateHOLFiniteState_skip]
  rw [BytesWrite.current_body,RlpWrite.BytesWrite.body_shape,evaluateHOLFiniteState_seq_line780,guard] at normal
  change evaluateHOLFiniteState source RlpWrite.BytesWrite.generalTail=(some (.returned value),target) at normal
  obtain ⟨callee,called,headerD,headerBase,headerN⟩:=RlpWrite.HeaderWrite.environment source.code.lookup dst 128#64 20#64
    (by simpa only [HeaderWrite.current_body] using HeaderWrite.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
      [localVar "dst",.const 128#64,localVar "n"]=some [.val (.word dst),.val (.word 128#64),.val (.word 20#64)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,d,n]
  rw [RlpWrite.BytesWrite.generalTail] at normal
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=CallNormal.scoped_normal source target "h" .one (ofString "rlp_write_header")
    [localVar "dst",.const 128#64,localVar "n"] _ HeaderWrite.body RlpWrite.BytesWrite.generalAfterHeader callee .one args called value normal
  have headerAnswer:=HeaderWrite.short_body_normal (callEntryStateHOLFinite source callee) child dst 20#64 (by decide) headerD headerN returned run
  let current:=CallNormal.continuationEntry source child "h" returned
  have hCell : current.locals.lookup (ofString "h")=some (.val (.word 1#64)):=by rw [CallNormal.continuation_lookup_same,headerAnswer]
  have nCell : current.locals.lookup (ofString "n")=some (.val (.word 20#64)):=
    (CallNormal.continuation_lookup_other source child "h" "n" returned (by decide)).trans n
  rw [RlpWrite.BytesWrite.generalAfterHeader] at continued
  obtain ⟨copied,copyRun,returnRun⟩:=sequence_returned current inner _ _ value
    (fun answer=>NoReturn.ignored_call (ofString "memcpy") _ current answer) continued
  have finalH : copied.locals.lookup (ofString "h")=some (.val (.word 1#64)):=
    (CallNormal.ignored_lookup current copied (ofString "h") (ofString "memcpy") _ copyRun).trans hCell
  have finalN : copied.locals.lookup (ofString "n")=some (.val (.word 20#64)):=
    (CallNormal.ignored_lookup current copied (ofString "n") (ofString "memcpy") _ copyRun).trans nCell
  obtain ⟨observed,innerEq⟩:=return_normal copied inner (.op .add [localVar "h",localVar "n"]) value returnRun
  have expected : eval copied (.op .add [localVar "h",localVar "n"])=some (.val (.word 21#64)):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,finalH,finalN,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact Option.some.inj (observed.symm.trans expected)

namespace FinishList

def body : ProgHOL 64:=match Guest.Software.guestFn_rlp_finish_list with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "dst",.one),(ofString "payload_end",.one)]
def payloadExpression : ExpHOL 64:=.op .sub [localVar "payload_end",.op .add [localVar "dst",.const 9#64]]
def copyArguments : List (ExpHOL 64):=[.op .add [localVar "dst",localVar "hl"],.op .add [localVar "dst",.const 9#64],localVar "payload"]
def copyCall : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") copyArguments
def headerArguments : List (ExpHOL 64):=[localVar "dst",localVar "payload"]
def headerCall : ProgHOL 64:=.call (some (none,none)) (ofString "rlp_encode_list_header") headerArguments
def returnLength : ProgHOL 64:=.return (.op .add [localVar "hl",localVar "payload"])
def afterHeaderLength : ProgHOL 64:=.seq copyCall (.seq headerCall returnLength)
def afterPayload : ProgHOL 64:=.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload"] afterHeaderLength

set_option maxRecDepth 100000 in
theorem body_shape : body=.dec (ofString "payload") .one payloadExpression afterPayload := by
  simp only [body,Guest.Software.guestFn_rlp_finish_list,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    payloadExpression,afterPayload,afterHeaderLength,copyCall,copyArguments,headerCall,headerArguments,returnLength,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_finish_list")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 774 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_rlp_finish_list) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_rlp_finish_list,
    paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using checked

/-- The unchanged list finisher on the real 64-byte withdrawal buffer.
It moves at most48 payload bytes inside that buffer, writes the actual
list header and derives its positive bounded final size and write frame. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena buffer 64) (lower : 9≤position) (upper : position≤57)
    (dst : source.locals.lookup (ofString "dst")=some (.val (.word buffer)))
    (finish : source.locals.lookup (ofString "payload_end")=some (.val (.word (buffer+BitVec.ofNat 64 position))))
    (funded : 100≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤57 ∧ paid≤100 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      WriteFrame source target buffer 64 := by
  let payload:=position-9
  have payloadBound : payload≤48:=by dsimp [payload]; omega
  have endNumber : (buffer+BitVec.ofNat 64 position).toNat=buffer.toNat+position:=
    byteAddress_toNat buffer position (by have room:=arena.upper; omega)
  have baseNumber : (buffer+9#64).toNat=buffer.toNat+9:=byteAddress_toNat buffer 9 (by have room:=arena.upper; omega)
  have difference : buffer+BitVec.ofNat 64 position-(buffer+9#64)=BitVec.ofNat 64 payload:=by
    apply BitVec.eq_of_toNat_eq
    have ordered : buffer+9#64≤buffer+BitVec.ofNat 64 position:=by change (buffer+9#64).toNat≤(buffer+BitVec.ofNat 64 position).toNat; omega
    rw [BitVec.toNat_sub_of_le ordered,endNumber,baseNumber,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    dsimp [payload]; omega
  have payloadRead : eval source payloadExpression=some (.val (.word (BitVec.ofNat 64 payload))):=by
    simp [eval,payloadExpression,evalHOLExact,evalListHOLExact,toExact,localVar,dst,finish,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  let sp:=bind source "payload" (BitVec.ofNat 64 payload)
  have payloadCell : sp.locals.lookup (ofString "payload")=some (.val (.word (BitVec.ofNat 64 payload))):=bind_lookup_same _ _ _
  have dstP : sp.locals.lookup (ofString "dst")=some (.val (.word buffer)):=
    (bind_lookup_other _ "payload" "dst" _ (by decide)).trans dst
  have tailCodes:=HeaderSuffix.tail_codes source installed
  have beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one):=by
    simpa only [BeLength.current_body,RlpLength.Be.formals] using BeLength.original_code source.code installed
  have headerCode : source.code.lookup (ofString "rlp_write_header")=some (RlpWrite.HeaderWrite.formals,RlpWrite.HeaderWrite.body,.one):=by
    simpa only [HeaderWrite.current_body] using HeaderWrite.original_code source.code installed
  have putCode : source.code.lookup (ofString "rlp_put_be")=some (RlpWrite.PutBe.formals,RlpWrite.PutBe.body,.one):=by
    simpa only [PutBe.current_body] using PutBe.original_code source.code installed
  have lengthArgs : evalListHOLFinite sp (h:=fun query=>Classical.propDecidable (sp.memaddrs query)) [localVar "payload"]=some [.val (.word (BitVec.ofNat 64 payload))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,payloadCell]
  obtain ⟨hl,headerPaid,hlLow,hlHigh,headerBound,lengthRun⟩:=RlpLength.ListHeader.call_execute sp (BitVec.ofNat 64 payload) "hl" [localVar "payload"] afterHeaderLength
    lengthArgs tailCodes.listLength tailCodes.headerLength beCode (by change 11≤source.clock; omega)
  let sh:=bind {sp with clock:=sp.clock-1-headerPaid} "hl" (BitVec.ofNat 64 hl)
  have dstH : sh.locals.lookup (ofString "dst")=some (.val (.word buffer)):=
    (bind_lookup_other _ "hl" "dst" _ (by decide)).trans dstP
  have payloadH : sh.locals.lookup (ofString "payload")=some (.val (.word (BitVec.ofNat 64 payload))):=
    (bind_lookup_other _ "hl" "payload" _ (by decide)).trans payloadCell
  have hlH : sh.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))):=bind_lookup_same _ _ _
  have copyArgs : evalListHOLFinite sh (h:=fun query=>Classical.propDecidable (sh.memaddrs query)) copyArguments=
      some (CopyGeneral.values (buffer+BitVec.ofNat 64 hl) (buffer+9#64) payload):=by
    simp [copyArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dstH,payloadH,hlH,valueIsWord,valueWord,wordOpHOL,wordOp]
  have copyMapped : CopyContext.Mapped sh (buffer+9#64) (buffer+BitVec.ofNat 64 hl) payload:=
    AllocatedBytes.copy_mapped sh _ _ payload domain (arena.subrange buffer 64 9 payload (by omega)) (arena.subrange buffer 64 hl payload (by omega))
  have copyBound:=CopyGeneral.cost_le (buffer+9#64) (buffer+BitVec.ofNat 64 hl) payload
  have copyRun:=CopyGeneral.call_execute sh copyArguments (buffer+9#64) (buffer+BitVec.ofNat 64 hl) payload copyArgs
    (CopyGeneral.original_code source.code installed) copyMapped (by omega) (by change CopyGeneral.cost _ _ payload+1≤source.clock-1-headerPaid; omega)
  let copied:=CopyGeneral.callState sh (buffer+9#64) (buffer+BitVec.ofNat 64 hl) payload
  have dstC : copied.locals.lookup (ofString "dst")=some (.val (.word buffer)):=dstH
  have payloadC : copied.locals.lookup (ofString "payload")=some (.val (.word (BitVec.ofNat 64 payload))):=payloadH
  have hlC : copied.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))):=hlH
  have headerArgs : evalListHOLFinite copied (h:=fun query=>Classical.propDecidable (copied.memaddrs query)) headerArguments=
      some [.val (.word buffer),.val (.word (BitVec.ofNat 64 payload))]:=by
    simp [headerArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dstC,payloadC]
  have headerMapped : ∀ index<9,copied.memaddrs (panByteAlignHOL (width:=64) (buffer+BitVec.ofNat 64 index)):=by
    intro index inside
    exact AllocatedBytes.byte_mapped copied buffer 64 index domain arena (by omega)
  obtain ⟨written,writePaid,writeBound,writeRun,writeMemory⟩:=RlpWrite.ListWrite.call_execute copied buffer (BitVec.ofNat 64 payload) headerArguments headerArgs
    tailCodes.listWriter headerCode beCode putCode headerMapped (by change 20≤source.clock-1-headerPaid-(CopyGeneral.cost _ _ payload+1); omega)
  let final:={copied with memory:=written,clock:=copied.clock-1-writePaid}
  have returnRun : evaluateHOLFiniteState final returnLength=(some (.returned (.val (.word (BitVec.ofNat 64 (hl+payload))))),emptyLocalsHOLFinite final):=by
    simp [returnLength,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,show final.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 hl))) from hlC,
      show final.locals.lookup (ofString "payload")=some (.val (.word (BitVec.ofNat 64 payload))) from payloadC,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have tailRun : evaluateHOLFiniteState sh afterHeaderLength=(some (.returned (.val (.word (BitVec.ofNat 64 (hl+payload))))),emptyLocalsHOLFinite final):=by
    rw [afterHeaderLength,evaluateHOLFiniteState_seq_line780,show evaluateHOLFiniteState sh copyCall=(none,copied) from copyRun]
    change evaluateHOLFiniteState copied (.seq headerCall returnLength)=_
    rw [evaluateHOLFiniteState_seq_line780,show evaluateHOLFiniteState copied headerCall=(none,final) from writeRun]
    exact returnRun
  let th:=restore sp "hl" (emptyLocalsHOLFinite final)
  have headerRun : evaluateHOLFiniteState sp afterPayload=(some (.returned (.val (.word (BitVec.ofNat 64 (hl+payload))))),th):=by
    rw [afterPayload,lengthRun,tailRun]
  let target:=restore source "payload" th
  let paid:=headerPaid+CopyGeneral.cost (buffer+9#64) (buffer+BitVec.ofNat 64 hl) payload+writePaid+3
  have clockDifference : source.clock-1-headerPaid-(CopyGeneral.cost (buffer+9#64) (buffer+BitVec.ofNat 64 hl) payload+1)-1-writePaid=source.clock-paid:=by dsimp [paid]; omega
  have frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid}:=by
    change emptyLocalsHOLFinite {source with memory:=written,clock:=source.clock-1-headerPaid-(CopyGeneral.cost (buffer+9#64) (buffer+BitVec.ofNat 64 hl) payload+1)-1-writePaid}=_
    rw [clockDifference]
    rfl
  refine ⟨target,hl+payload,paid,by omega,by omega,by dsimp [paid]; omega,?_,frame,?_,?_⟩
  · rw [body_shape]
    exact ScalarScope.declare_execute source th "payload" payloadExpression (BitVec.ofNat 64 payload) afterPayload _ payloadRead headerRun
  · have metadata:=congrArg MemoryMetadata.erase frame
    exact metadata
  · intro query away
    have headerSame : written query=copied.memory query:=writeMemory query (fun index inside=>(away index (by omega)).2)
    have copiedSame : copied.memory query=sh.memory query:=CopyGeneral.call_memory_away sh (buffer+9#64) (buffer+BitVec.ofNat 64 hl) query payload (by
      intro offset inside
      simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using away (hl+offset) (by omega))
    exact headerSame.trans copiedSame

/-- Every list-finisher outcome, including short clocks, obeys the same
allowance. The caller supplies only its already owned buffer and position. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena buffer 64) (lower : 9≤position) (upper : position≤57)
    (dst : source.locals.lookup (ofString "dst")=some (.val (.word buffer)))
    (finish : source.locals.lookup (ofString "payload_end")=some (.val (.word (buffer+BitVec.ofNat 64 position)))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤100 := by
  by_cases funded : 100≤source.clock
  · obtain ⟨target,encoded,paid,positive,bounded,price,run,frame,memory⟩:=execute source buffer position installed domain arena lower upper dst finish funded
    have clocks:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at clocks
    rw [run]
    change source.clock-target.clock≤100
    omega
  · omega

/-- The same real list-finisher normal return derives its actual length
and bounded writes even when the entry clock is below the allowance. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (position : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena buffer 64) (lower : 9≤position) (upper : position≤57)
    (dst : source.locals.lookup (ofString "dst")=some (.val (.word buffer)))
    (finish : source.locals.lookup (ofString "payload_end")=some (.val (.word (buffer+BitVec.ofNat 64 position))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤57 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-target.clock≤100 ∧ WriteFrame source target buffer 64 := by
  let padded:={source with clock:=source.clock+100}
  obtain ⟨post,encoded,paid,positive,bounded,price,run,frame,memory⟩:=execute padded buffer position installed domain arena lower upper dst finish (by change 100≤source.clock+100; omega)
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned value)) target 100 ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+100}=post at endpoint
  rw [←endpoint] at memory
  have spent:=body_cost source buffer position installed domain arena lower upper dst finish
  rw [normal] at spent
  exact ⟨encoded,positive,bounded,answer,spent,⟨memory.metadata,memory.memory⟩⟩

end FinishList

end InitECandidate.Solver.Input.CurrentRlp

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.short_body_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.twenty_normal_value

#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.body_shape
#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.execute

#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.body_normal
