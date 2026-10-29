import InitECandidate.Solver.Input.CurrentRlp.BytesWrite
import InitECandidate.Solver.Input.NoReturnAtoms
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.CallPrefixFrameTrace
import InitECandidate.Solver.Input.CallPrefixCommand
import InitECandidate.Solver.WitnessRadix.AllocationNoWrapTrace
import InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix
import InitECandidate.Solver.Input.RlpLength.WithdrawalProgram
import InitECandidate.Solver.Input.InputImageFrame
import InitECandidate.Solver.WitnessRadix.AllocatedAwayBelow

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

namespace Withdrawal

def body : ProgHOL 64:=match Guest.Software.guestFn_encode_withdrawal_rlp with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "wd",.one)]
def returnShape : ShapeHOL:=.comb [.one,.one]
def advance : ProgHOL 64:=.assign .local (ofString "p") (.op .add [localVar "p",localVar "w"])
def wordArguments (offset : Nat) : List (ExpHOL 64):=[localVar "p",Scalar.flat64 (localVar "wd") (if offset=0 then [] else [offset])]
def addressArguments : List (ExpHOL 64):=[localVar "p",.op .add [localVar "wd",.const 16#64],.const 20#64]
def secondCall : ProgHOL 64:=.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_word") (wordArguments 8)
def addressCall : ProgHOL 64:=.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes") addressArguments
def thirdCall : ProgHOL 64:=.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_word") (wordArguments 36)
def finishArguments : List (ExpHOL 64):=[localVar "buf",localVar "p"]
def returnPair : ProgHOL 64:=.return (.rstruct [localVar "buf",localVar "total"])
def afterWords : ProgHOL 64:=.decCall (ofString "total") .one (ofString "rlp_finish_list") finishArguments returnPair
def afterThird : ProgHOL 64:=.seq advance afterWords
def afterAddress : ProgHOL 64:=.seq advance (.seq thirdCall afterThird)
def afterSecond : ProgHOL 64:=.seq advance (.seq addressCall afterAddress)
def afterFirst : ProgHOL 64:=.seq advance (.seq secondCall afterSecond)
def afterPointer : ProgHOL 64:=.decCall (ofString "w") .one (ofString "rlp_encode_word") (wordArguments 0) afterFirst
def afterBuffer : ProgHOL 64:=.dec (ofString "p") .one (.op .add [localVar "buf",.const 9#64]) afterPointer

set_option maxRecDepth 100000 in
theorem body_shape : body=.decCall (ofString "buf") .one (ofString "alloc") [.const 64#64] afterBuffer := by
  simp only [body,Guest.Software.guestFn_encode_withdrawal_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    afterBuffer,afterPointer,afterFirst,afterSecond,afterAddress,afterThird,afterWords,advance,secondCall,addressCall,thirdCall,wordArguments,addressArguments,
    finishArguments,returnPair,Scalar.flat64,Scalar.flat32,Scalar.flatAddress,Scalar.shift,localVar,List.nil_append,List.cons_append,List.append_nil]
  rfl

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "encode_withdrawal_rlp")=some (formals,body,returnShape) := by
  have checked:=OriginalCode.indexed code installed 779 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_encode_withdrawal_rlp) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,returnShape,Guest.Software.guestFn_encode_withdrawal_rlp,
    paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using checked

/-- The real withdrawal writer's live buffer, current position and copied
44-byte input record. All spans precede the independently derived future
heap frontier; no future helper normality is part of this contract. -/
structure Writer (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer buffer : BitVec 64) (start position : Nat) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  bufferArena : AllocatedBytes.Arena buffer 64
  bufferAligned : buffer.toNat%8=0
  inputArena : AllocatedBytes.Arena pointer (input.length%2^64)
  inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat
  heap : Blob.HeapInput source input pointer
  inside : start+44≤input.length%2^64
  wdCell : source.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start)))
  bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer))
  positionCell : source.locals.lookup (ofString "p")=some (.val (.word (buffer+BitVec.ofNat 64 position)))

/-- A same-execution bounded writer frame keeps every input byte and all
nonlocal state needed by the next scalar read. Only the next real local
bindings are supplied separately. -/
theorem Writer.of_write {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (frame : WriteFrame source target buffer 64) (nextPosition : Nat)
    (wd : target.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (buf : target.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (p : target.locals.lookup (ofString "p")=some (.val (.word (buffer+BitVec.ofNat 64 nextPosition)))) :
    Writer input target pointer buffer start nextPosition := by
  have domain:=MemoryMetadata.domain frame.metadata
  change target.memaddrs=source.memaddrs at domain
  have endian:=MemoryMetadata.endian frame.metadata
  change target.be=source.be at endian
  have code:=MemoryMetadata.code frame.metadata
  change target.code=source.code at code
  refine ⟨by rw [code]; exact model.installed,domain.trans model.domain,model.bufferArena,model.bufferAligned,model.inputArena,model.inputBefore,?_,model.inside,wd,buf,p⟩
  apply Blob.HeapInput.of_words source target input pointer model.heap domain endian
  intro offset inside
  have number:=byteAddress_toNat pointer offset (by have room:=model.inputArena.upper; omega)
  have backing:=AllocatedBytes.aligned_number (pointer+BitVec.ofNat 64 offset)
  have below : (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 offset)).toNat<buffer.toNat:=by
    change (pointer+BitVec.ofNat 64 offset).toNat=pointer.toNat+offset at number
    have before:=model.inputBefore
    omega
  exact frame.memory _ (model.bufferArena.away_below buffer _ 64 model.bufferAligned below)

/-- The current flattened scalar expression reads the same actual input
record at each of the writer's three word positions. -/
theorem Writer.scalar_read {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (offset : Nat) (inside : offset≤36) :
    eval source (Scalar.flat64 (localVar "wd") (if offset=0 then [] else [offset]))=
      some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+offset))))) := by
  exact RlpLength.Withdrawal.scalar_read source input pointer start offset model.heap (by have limit:=model.inside; omega) model.wdCell

def wordCall (offset : Nat) : ProgHOL 64:=.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_word") (wordArguments offset)

/-- The actual current word writer reads the same copied withdrawal
scalar and costs at most nineteen ticks including its assigned caller. -/
theorem Writer.word_call_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (offset : Nat) (inside : offset≤36) : source.clock-(evaluateHOLFiniteState source (wordCall offset)).2.clock≤19 := by
  have scalar:=model.scalar_read offset inside
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (wordArguments offset)=
      some [.val (.word (buffer+BitVec.ofNat 64 position)),.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+offset))))]:=by
    simp only [eval] at scalar
    simp only [wordArguments,evalListHOLFinite,evalListHOLExact,scalar]
    simp [evalHOLExact,toExact,localVar,model.positionCell]
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup (buffer+BitVec.ofNat 64 position)
    (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+offset))) (WordWrite.original_code source.code model.installed)
  exact ClockCost.call_current source (some (some (ofString "w"))) (ofString "rlp_encode_word") (wordArguments offset) _ WordWrite.body callee .one 18
    args called (WordWrite.body_cost (callEntryStateHOLFinite source callee) _ _ model.installed d w)

/-- A real normal assigned word writer derives its new length, actual
local update and complete retained input/buffer context for the next step. -/
theorem Writer.word_call_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (offset : Nat) (inside : offset≤36) (room : position+9≤64)
    (normal : evaluateHOLFiniteState source (wordCall offset)=(none,target)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ target.locals=source.locals.update (ofString "w",.val (.word (BitVec.ofNat 64 encoded))) ∧
      target.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      Writer input target pointer buffer start position ∧ WriteFrame source target buffer 64 := by
  have scalar:=model.scalar_read offset inside
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (wordArguments offset)=
      some [.val (.word (buffer+BitVec.ofNat 64 position)),.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+offset))))]:=by
    simp only [eval] at scalar
    simp only [wordArguments,evalListHOLFinite,evalListHOLExact,scalar]
    simp [evalHOLExact,toExact,localVar,model.positionCell]
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup (buffer+BitVec.ofNat 64 position)
    (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+offset))) (WordWrite.original_code source.code model.installed)
  obtain ⟨funded,child,returned,run,endpoint⟩:=CallNormal.local_known source target (ofString "w") (ofString "rlp_encode_word") (wordArguments offset) _
    WordWrite.body callee .one args called normal
  obtain ⟨encoded,positive,bounded,answer,price,frame⟩:=WordWrite.body_normal (callEntryStateHOLFinite source callee) child
    (buffer+BitVec.ofNat 64 position) (BitVec.ofNat 64 (Guest.GasLimit.le64 input (start+offset))) model.installed d w returned run
  have finalFrame : WriteFrame source target buffer 64:=by
    rw [endpoint,answer]
    exact (show WriteFrame source (bind {child with locals:=source.locals} "w" (BitVec.ofNat 64 encoded)) (buffer+BitVec.ofNat 64 position) 9 from
      ⟨frame.metadata,frame.memory⟩).shift buffer position 9 64 room
  have localsEq : target.locals=source.locals.update (ofString "w",.val (.word (BitVec.ofNat 64 encoded))):=by
    rw [endpoint,answer]
    rfl
  have saved (name : String) (other : ofString "w"≠ofString name) : target.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,other]
  have current:=model.of_write finalFrame position ((saved "wd" (by decide)).trans model.wdCell)
    ((saved "buf" (by decide)).trans model.bufferCell) ((saved "p" (by decide)).trans model.positionCell)
  exact ⟨encoded,positive,bounded,localsEq,by rw [localsEq]; simp [HolFiniteMapExact.update,FUPDATE],current,finalFrame⟩

/-- The actual pointer assignment advances by the returned encoded size,
retaining the same input, heap and already written buffer bytes. -/
theorem Writer.advance_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position) (encoded : Nat)
    (w : source.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (normal : evaluateHOLFiniteState source advance=(none,target)) :
    Writer input target pointer buffer start (position+encoded) ∧ WriteFrame source target buffer 64 := by
  have read : eval source (.op .add [localVar "p",localVar "w"])=some (.val (.word (buffer+BitVec.ofNat 64 (position+encoded)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,model.positionCell,w,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add,BitVec.add_assoc]
  have executed:=StateSteps.assign_execute source "p" (.op .add [localVar "p",localVar "w"]) (buffer+BitVec.ofNat 64 position)
    (buffer+BitVec.ofNat 64 (position+encoded)) model.positionCell read
  have endpoint : target=bind source "p" (buffer+BitVec.ofNat 64 (position+encoded)):=congrArg Prod.snd (normal.symm.trans executed)
  have frame : WriteFrame source target buffer 64:=by rw [endpoint]; exact ⟨rfl,by intros; rfl⟩
  have wd : target.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))):=by
    rw [endpoint]
    exact (bind_lookup_other _ "p" "wd" _ (by decide)).trans model.wdCell
  have buf : target.locals.lookup (ofString "buf")=some (.val (.word buffer)):=by
    rw [endpoint]
    exact (bind_lookup_other _ "p" "buf" _ (by decide)).trans model.bufferCell
  have p : target.locals.lookup (ofString "p")=some (.val (.word (buffer+BitVec.ofNat 64 (position+encoded)))):=by rw [endpoint]; exact bind_lookup_same _ _ _
  exact ⟨model.of_write frame (position+encoded) wd buf p,frame⟩

/-- The address writer's real arguments are the current position and
its owned twenty bytes inside the same original withdrawal record. -/
theorem Writer.address_args {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) addressArguments=
      some [.val (.word (buffer+BitVec.ofNat 64 position)),.val (.word (pointer+BitVec.ofNat 64 (start+16))),.val (.word 20#64)] := by
  simp [addressArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.positionCell,model.wdCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add,BitVec.add_assoc]

theorem Writer.address_call_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (room : position+29≤64) : source.clock-(evaluateHOLFiniteState source addressCall).2.clock≤41 := by
  obtain ⟨callee,called,d,s,n⟩:=RlpWrite.BytesWrite.environment source.code.lookup (buffer+BitVec.ofNat 64 position) (pointer+BitVec.ofNat 64 (start+16)) 20#64
    (BytesWrite.original_code source.code model.installed)
  have inputArena : AllocatedBytes.Arena (pointer+BitVec.ofNat 64 (start+16)) 20:=model.inputArena.subrange pointer _ (start+16) 20 (by have extent:=model.inside; omega)
  have outputArena : AllocatedBytes.Arena (buffer+BitVec.ofNat 64 position) 29:=model.bufferArena.subrange buffer 64 position 29 room
  exact ClockCost.call_current source (some (some (ofString "w"))) (ofString "rlp_encode_bytes") addressArguments _ BytesWrite.body callee .one 40
    model.address_args called (BytesWrite.body_cost (callEntryStateHOLFinite source callee) _ _ 20 (by decide) model.installed model.domain d s n inputArena outputArena)

/-- The real assigned address writer returns exactly21, retains the next
word's input and keeps its writes inside the original64-byte buffer. -/
theorem Writer.address_call_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (room : position+29≤64) (normal : evaluateHOLFiniteState source addressCall=(none,target)) :
    target.locals=source.locals.update (ofString "w",.val (.word 21#64)) ∧ target.locals.lookup (ofString "w")=some (.val (.word 21#64)) ∧
      Writer input target pointer buffer start position ∧ WriteFrame source target buffer 64 := by
  obtain ⟨callee,called,d,s,n⟩:=RlpWrite.BytesWrite.environment source.code.lookup (buffer+BitVec.ofNat 64 position) (pointer+BitVec.ofNat 64 (start+16)) 20#64
    (BytesWrite.original_code source.code model.installed)
  obtain ⟨funded,child,returned,run,endpoint⟩:=CallNormal.local_known source target (ofString "w") (ofString "rlp_encode_bytes") addressArguments _
    BytesWrite.body callee .one model.address_args called normal
  have inputArena : AllocatedBytes.Arena (pointer+BitVec.ofNat 64 (start+16)) 20:=model.inputArena.subrange pointer _ (start+16) 20 (by have extent:=model.inside; omega)
  have outputArena : AllocatedBytes.Arena (buffer+BitVec.ofNat 64 position) 29:=model.bufferArena.subrange buffer 64 position 29 room
  obtain ⟨encoded,lower,positive,bounded,number,answer,price,frame⟩:=BytesWrite.body_normal (callEntryStateHOLFinite source callee) child
    (buffer+BitVec.ofNat 64 position) (pointer+BitVec.ofNat 64 (start+16)) 20 (by decide) model.installed model.domain d s n inputArena outputArena returned run
  have answer21:=BytesWrite.twenty_normal_value (callEntryStateHOLFinite source callee) child _ _ model.installed d s n returned run
  have finalFrame : WriteFrame source target buffer 64:=by
    rw [endpoint,answer21]
    exact (show WriteFrame source (bind {child with locals:=source.locals} "w" 21#64) (buffer+BitVec.ofNat 64 position) 29 from
      ⟨frame.metadata,frame.memory⟩).shift buffer position 29 64 room
  have localsEq : target.locals=source.locals.update (ofString "w",.val (.word 21#64)):=by rw [endpoint,answer21]; rfl
  have saved (name : String) (other : ofString "w"≠ofString name) : target.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,other]
  have current:=model.of_write finalFrame position ((saved "wd" (by decide)).trans model.wdCell)
    ((saved "buf" (by decide)).trans model.bufferCell) ((saved "p" (by decide)).trans model.positionCell)
  exact ⟨localsEq,by rw [localsEq]; simp [HolFiniteMapExact.update,FUPDATE],current,finalFrame⟩

/-- The actual list-finisher caller and final pair return, at the position
supplied by the preceding four real field writers, on every outcome. -/
theorem Writer.finish_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (lower : 9≤position) (upper : position≤57) : source.clock-(evaluateHOLFiniteState source afterWords).2.clock≤101 := by
  obtain ⟨callee,called,d,p⟩:=word_pair_environment source.code.lookup (ofString "rlp_finish_list") (ofString "dst") (ofString "payload_end")
    FinishList.body .one buffer (buffer+BitVec.ofNat 64 position) (by decide) (FinishList.original_code source.code model.installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) finishArguments=
      some [.val (.word buffer),.val (.word (buffer+BitVec.ofNat 64 position))]:=by
    simp [finishArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.bufferCell,model.positionCell]
  rw [afterWords]
  exact ClockCost.scoped_reached_current source "total" .one (ofString "rlp_finish_list") finishArguments _ FinishList.body returnPair callee .one 100 0 args called
    (FinishList.body_cost (callEntryStateHOLFinite source callee) buffer position model.installed model.domain model.bufferArena lower upper d p)
    (by
      intro child returned normal checked
      let current:=CallNormal.continuationEntry source child "total" returned
      exact ClockCost.returned current.code (.rstruct [localVar "buf",localVar "total"]) current rfl)

/-- The same observed final list call supplies the actual encoded pair,
owned positive output and retained physical writer frame. -/
theorem Writer.finish_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (lower : 9≤position) (upper : position≤57) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterWords=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤57 ∧ value=.rStruct [.val (.word buffer),.val (.word (BitVec.ofNat 64 encoded))] ∧ WriteFrame source target buffer 64 := by
  obtain ⟨callee,called,d,p⟩:=word_pair_environment source.code.lookup (ofString "rlp_finish_list") (ofString "dst") (ofString "payload_end")
    FinishList.body .one buffer (buffer+BitVec.ofNat 64 position) (by decide) (FinishList.original_code source.code model.installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) finishArguments=
      some [.val (.word buffer),.val (.word (buffer+BitVec.ofNat 64 position))]:=by
    simp [finishArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.bufferCell,model.positionCell]
  rw [afterWords] at normal
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=CallNormal.scoped_normal source target "total" .one (ofString "rlp_finish_list")
    finishArguments _ FinishList.body returnPair callee .one args called value normal
  obtain ⟨encoded,positive,bounded,answer,price,frame⟩:=FinishList.body_normal (callEntryStateHOLFinite source callee) child buffer position
    model.installed model.domain model.bufferArena lower upper d p returned run
  let current:=CallNormal.continuationEntry source child "total" returned
  have buf : current.locals.lookup (ofString "buf")=some (.val (.word buffer)):=
    (CallNormal.continuation_lookup_other source child "total" "buf" returned (by decide)).trans model.bufferCell
  have total : current.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 encoded))):=by rw [CallNormal.continuation_lookup_same,answer]
  obtain ⟨observed,innerEq⟩:=return_normal current inner (.rstruct [localVar "buf",localVar "total"]) value continued
  have expected : eval current (.rstruct [localVar "buf",localVar "total"])=some (.rStruct [.val (.word buffer),.val (.word (BitVec.ofNat 64 encoded))]):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,buf,total]
  refine ⟨encoded,positive,bounded,Option.some.inj (observed.symm.trans expected),?_⟩
  rw [endpoint,innerEq]
  exact ⟨frame.metadata,frame.memory⟩

theorem advance_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    source.clock-(evaluateHOLFiniteState source advance).2.clock≤0 :=
  ClockCost.of_quiet source.code advance (QuietClock.assign source.code _ _) source rfl

/-- After the final actual word return, pointer advance and the genuine
list-finisher suffix account for every outcome in101source ticks. -/
theorem Writer.after_third_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (encoded : Nat) (w : source.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (lower : 9≤position+encoded) (upper : position+encoded≤57) : source.clock-(evaluateHOLFiniteState source afterThird).2.clock≤101 := by
  rw [afterThird]
  exact ClockCost.sequence_reached_current source advance afterWords 0 101 (advance_cost source) (by
    intro current normal
    obtain ⟨next,frame⟩:=model.advance_normal encoded w normal
    exact next.finish_cost lower upper)

/-- The third word call is reached only after the actual address length
has advanced the pointer; its normal output supplies the final position. -/
theorem Writer.after_address_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (w : source.locals.lookup (ofString "w")=some (.val (.word 21#64))) (upper : position+21≤48) :
    source.clock-(evaluateHOLFiniteState source afterAddress).2.clock≤120 := by
  rw [afterAddress]
  exact ClockCost.sequence_reached_current source advance (.seq thirdCall afterThird) 0 120 (advance_cost source) (by
    intro current normal
    obtain ⟨next,frame⟩:=model.advance_normal 21 w normal
    exact ClockCost.sequence_reached_current current thirdCall afterThird 19 101 (next.word_call_cost 36 (by decide)) (by
      intro target callRun
      obtain ⟨encoded,positive,bounded,localsEq,wCell,final,memory⟩:=next.word_call_normal 36 (by decide) (by omega) callRun
      exact final.after_third_cost encoded wCell (by omega) (by omega)))

/-- The address-call price is combined only with its same-run exact21-byte
normal result, keeping the third word inside the original buffer. -/
theorem Writer.after_second_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (encoded : Nat) (w : source.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (upper : position+encoded≤27) : source.clock-(evaluateHOLFiniteState source afterSecond).2.clock≤161 := by
  rw [afterSecond]
  exact ClockCost.sequence_reached_current source advance (.seq addressCall afterAddress) 0 161 (advance_cost source) (by
    intro current normal
    obtain ⟨next,frame⟩:=model.advance_normal encoded w normal
    exact ClockCost.sequence_reached_current current addressCall afterAddress 41 120 (next.address_call_cost (by omega)) (by
      intro target callRun
      obtain ⟨localsEq,wCell,final,memory⟩:=next.address_call_normal (by omega) callRun
      exact final.after_address_cost wCell (by omega)))

/-- Every outcome of the unchanged suffix after the first word is bounded,
including both assigned word writers, the address writer and list finisher. -/
theorem Writer.after_first_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start position : Nat} (model : Writer input source pointer buffer start position)
    (encoded : Nat) (w : source.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (upper : position+encoded≤18) : source.clock-(evaluateHOLFiniteState source afterFirst).2.clock≤180 := by
  rw [afterFirst]
  exact ClockCost.sequence_reached_current source advance (.seq secondCall afterSecond) 0 180 (advance_cost source) (by
    intro current normal
    obtain ⟨next,frame⟩:=model.advance_normal encoded w normal
    exact ClockCost.sequence_reached_current current secondCall afterSecond 19 161 (next.word_call_cost 8 (by decide)) (by
      intro target callRun
      obtain ⟨encodedNext,positive,bounded,localsEq,wCell,final,memory⟩:=next.word_call_normal 8 (by decide) (by omega) callRun
      exact final.after_second_cost encodedNext wCell (by omega)))

/-- The first real scoped word call supplies its own encoded length and
restored current writer context; no normal suffix is assumed. -/
theorem Writer.after_pointer_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start : Nat} (model : Writer input source pointer buffer start 9) :
    source.clock-(evaluateHOLFiniteState source afterPointer).2.clock≤199 := by
  have scalar:=model.scalar_read 0 (by decide)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (wordArguments 0)=
      some [.val (.word (buffer+9#64)),.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)))]:=by
    simp only [eval] at scalar
    simp only [wordArguments,evalListHOLFinite,evalListHOLExact,scalar]
    simpa [evalHOLExact,toExact,localVar,model.positionCell] using scalar
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup (buffer+9#64)
    (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)) (WordWrite.original_code source.code model.installed)
  rw [afterPointer]
  exact ClockCost.scoped_reached_current source "w" .one (ofString "rlp_encode_word") (wordArguments 0) _ WordWrite.body afterFirst callee .one 18 180 args called
    (WordWrite.body_cost (callEntryStateHOLFinite source callee) _ _ model.installed d w) (by
      intro child returned normal checked
      obtain ⟨encoded,positive,bounded,answer,price,frame⟩:=WordWrite.body_normal (callEntryStateHOLFinite source callee) child
        (buffer+9#64) (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)) model.installed d w returned normal
      let current:=CallNormal.continuationEntry source child "w" returned
      have totalFrame : WriteFrame source current buffer 64:=
        (show WriteFrame source current (buffer+9#64) 9 from ⟨frame.metadata,frame.memory⟩).shift buffer 9 9 64 (by decide)
      have wd : current.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))):=
        (CallNormal.continuation_lookup_other source child "w" "wd" returned (by decide)).trans model.wdCell
      have buf : current.locals.lookup (ofString "buf")=some (.val (.word buffer)):=
        (CallNormal.continuation_lookup_other source child "w" "buf" returned (by decide)).trans model.bufferCell
      have p : current.locals.lookup (ofString "p")=some (.val (.word (buffer+9#64))):=
        (CallNormal.continuation_lookup_other source child "w" "p" returned (by decide)).trans model.positionCell
      have wCell : current.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=by rw [CallNormal.continuation_lookup_same,answer]
      exact (model.of_write totalFrame 9 wd buf p).after_first_cost encoded wCell (by omega))

/-- The pure initial position declaration exposes the exact writer model
at buffer+9. Its metadata and bytes are those already owned by the caller. -/
theorem after_buffer_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer buffer : BitVec 64) (start : Nat)
    (model : Writer input (bind source "p" (buffer+9#64)) pointer buffer start 9) :
    source.clock-(evaluateHOLFiniteState source afterBuffer).2.clock≤199 := by
  have buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)):=by
    simpa [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using model.bufferCell
  have read : eval source (.op .add [localVar "buf",.const 9#64])=some (.val (.word (buffer+9#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,buf,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [afterBuffer]
  exact ClockCost.declared_current source "p" _ (buffer+9#64) afterPointer 199 read model.after_pointer_cost

/-- Current physical entry for one44-byte withdrawal. The actual buffer
allocation remains to be executed; only the older input and current heap
are supplied. Its own capacity check derives all future buffer room. -/
structure Entry (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap : BitVec 64) (start : Nat) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  inputArena : AllocatedBytes.Arena pointer (input.length%2^64)
  inputBefore : pointer.toNat+input.length%2^64≤heap.toNat
  image : Blob.HeapInput source input pointer
  inside : start+44≤input.length%2^64
  wdCell : source.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start)))

/-- Complete unchanged current779, including the genuine allocation,
all four field writers, list movement/header and final pair return. Every
outcome is covered, with no successful allocation or writer oracle. -/
theorem body_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer heap : BitVec 64} {start : Nat} (entry : Entry input source pointer heap start) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤201 := by
  let output:=evaluateHOLFiniteState source body
  have actual : evaluateHOLFiniteState source (.decCall (ofString "buf") .one (ofString "alloc") [.const 64#64] afterBuffer)=(output.1,output.2):=by
    rw [←body_shape]
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 64#64]=some (PersistentAlloc.values 64#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  have noWrap : heap.toNat+(64#64 : BitVec 64).toNat+7<2^64:=by have upper:=entry.heapBound; change heap.toNat+64+7<2^64; omega
  rcases PersistentAlloc.scoped_trace_no_wrap source output.2 "buf" [.const 64#64] afterBuffer heap 64#64 args entry.installed entry.heapCell noWrap output.1 actual with stopped|reached
  · exact Nat.le_trans stopped (by decide)
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let current:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 64#64) "buf" heap
    let ready:=bind current "p" (heap+9#64)
    have wd : ready.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))):=
      (bind_lookup_other current "p" "wd" _ (by decide)).trans ((bind_lookup_other _ "buf" "wd" _ (by decide)).trans entry.wdCell)
    have buf : ready.locals.lookup (ofString "buf")=some (.val (.word heap)):=
      (bind_lookup_other current "p" "buf" _ (by decide)).trans (bind_lookup_same _ _ _)
    have model : Writer input ready pointer heap start 9:={
      installed:=entry.installed,domain:=entry.domain,bufferArena:=⟨entry.heapArena.lower,by change heap.toNat+64≤2952790016 at room; omega⟩
      bufferAligned:=entry.heapAligned,inputArena:=entry.inputArena,inputBefore:=entry.inputBefore
      heap:=Blob.HeapInput.of_fields source ready input pointer rfl rfl rfl entry.image,inside:=entry.inside,wdCell:=wd,bufferCell:=buf,positionCell:=bind_lookup_same _ _ _ }
    have remaining:=after_buffer_cost input current pointer heap start model
    rw [continued] at remaining
    change source.clock-1-inner.clock≤199 at remaining
    change source.clock-output.2.clock≤201
    have clocks:=congrArg PanSemStateFiniteExact.clock endpoint
    change output.2.clock=inner.clock at clocks
    rw [clocks]
    omega

def fieldActions : List CallPrefix.Action:=[.command advance,.command secondCall,.command advance,.command addressCall,.command advance,.command thirdCall,.command advance]

theorem field_shape : afterFirst=CallPrefix.program fieldActions afterWords := rfl

theorem field_never : NoReturn.Never (CallPrefix.program fieldActions .skip) := by
  have assignSafe : LocalPrefix (ofString "wd") advance:=.assign (ofString "p") _ (by decide)
  have wordSafe (offset : Nat) : LocalPrefix (ofString "wd") (wordCall offset):=
    .call (some (ofString "w")) (ofString "rlp_encode_word") (wordArguments offset) (by intro name same; cases same; decide)
  have addressSafe : LocalPrefix (ofString "wd") addressCall:=
    .call (some (ofString "w")) (ofString "rlp_encode_bytes") addressArguments (by intro name same; cases same; decide)
  have safe : LocalPrefix (ofString "wd") (CallPrefix.program fieldActions .skip):=
    .seq assignSafe (.seq (wordSafe 8) (.seq assignSafe (.seq addressSafe (.seq assignSafe (.seq (wordSafe 36) (.seq assignSafe .skip))))))
  intro F source value
  exact (safe.summary_full source).2.1 value

/-- The seven actual commands after the first word retain the original
input and derive the final position. Every intermediate record length,
assigned caller and p update comes from this same prefix execution. -/
theorem Writer.fields_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start : Nat} (model : Writer input source pointer buffer start 9)
    (first : Nat) (firstPositive : 1≤first) (firstBound : first≤9)
    (w : source.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 first))))
    (execution : CallPrefix.Execution source fieldActions target) :
    ∃ position,9≤position ∧ position≤57 ∧ Writer input target pointer buffer start position ∧ WriteFrame source target buffer 64 := by
  obtain ⟨s1,advance1,e1⟩:=execution.command_next advance _
  obtain ⟨m1,f1⟩:=model.advance_normal first w advance1
  obtain ⟨s2,word2,e2⟩:=e1.command_next secondCall _
  obtain ⟨second,secondPositive,secondBound,locals2,w2,m2,f2⟩:=m1.word_call_normal 8 (by decide) (by omega) word2
  obtain ⟨s3,advance2,e3⟩:=e2.command_next advance _
  obtain ⟨m3,f3⟩:=m2.advance_normal second w2 advance2
  obtain ⟨s4,address,e4⟩:=e3.command_next addressCall _
  obtain ⟨locals4,w4,m4,f4⟩:=m3.address_call_normal (by omega) address
  obtain ⟨s5,advance3,e5⟩:=e4.command_next advance _
  obtain ⟨m5,f5⟩:=m4.advance_normal 21 w4 advance3
  obtain ⟨s6,word3,e6⟩:=e5.command_next thirdCall _
  obtain ⟨third,thirdPositive,thirdBound,locals6,w6,m6,f6⟩:=m5.word_call_normal 36 (by decide) (by omega) word3
  obtain ⟨s7,advance4,e7⟩:=e6.command_next advance _
  obtain ⟨m7,f7⟩:=m6.advance_normal third w6 advance4
  have endpoint : target=s7:=by cases e7; rfl
  rw [endpoint]
  exact ⟨((9+first)+second)+21+third,by omega,by omega,m7,((((f1.trans f2).trans f3).trans f4).trans f5).trans (f6.trans f7)⟩

/-- Every actual normal field suffix reaches the genuine final list call
with its own derived bounded position and returns the resulting encoded
pair, retaining the complete input/buffer write frame. -/
theorem Writer.after_first_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start : Nat} (model : Writer input source pointer buffer start 9)
    (first : Nat) (firstPositive : 1≤first) (firstBound : first≤9)
    (w : source.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 first))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterFirst=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤57 ∧ value=.rStruct [.val (.word buffer),.val (.word (BitVec.ofNat 64 encoded))] ∧ WriteFrame source target buffer 64 := by
  rw [field_shape] at normal
  obtain ⟨middle,inner,execution,remaining,clocks,outputFrame⟩:=CallPrefix.normal_frame_trace source target fieldActions afterWords value field_never normal
  obtain ⟨position,lower,upper,final,prefixFrame⟩:=model.fields_normal first firstPositive firstBound w execution
  obtain ⟨encoded,positive,bounded,answer,finishFrame⟩:=final.finish_normal lower upper value remaining
  have total:=prefixFrame.trans finishFrame
  have memoryEq:=LocalEffects.memory_of_erase inner target outputFrame
  exact ⟨encoded,positive,bounded,answer,⟨(MemoryMetadata.of_frame outputFrame).trans total.metadata,
    fun query away=>(congrFun memoryEq query).trans (total.memory query away)⟩⟩

/-- The observed first scoped word return supplies its real length and
buffer context before the remaining actual field execution. -/
theorem Writer.after_pointer_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer buffer : BitVec 64} {start : Nat} (model : Writer input source pointer buffer start 9)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterPointer=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤57 ∧ value=.rStruct [.val (.word buffer),.val (.word (BitVec.ofNat 64 encoded))] ∧ WriteFrame source target buffer 64 := by
  have scalar:=model.scalar_read 0 (by decide)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (wordArguments 0)=
      some [.val (.word (buffer+9#64)),.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)))]:=by
    simp only [eval] at scalar
    simp only [wordArguments,evalListHOLFinite,evalListHOLExact,scalar]
    simpa [evalHOLExact,toExact,localVar,model.positionCell] using scalar
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup (buffer+9#64)
    (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)) (WordWrite.original_code source.code model.installed)
  rw [afterPointer] at normal
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=CallNormal.scoped_normal source target "w" .one (ofString "rlp_encode_word")
    (wordArguments 0) _ WordWrite.body afterFirst callee .one args called value normal
  obtain ⟨first,firstPositive,firstBound,answer,price,frame⟩:=WordWrite.body_normal (callEntryStateHOLFinite source callee) child
    (buffer+9#64) (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)) model.installed d w returned run
  let current:=CallNormal.continuationEntry source child "w" returned
  have firstFrame : WriteFrame source current buffer 64:=
    (show WriteFrame source current (buffer+9#64) 9 from ⟨frame.metadata,frame.memory⟩).shift buffer 9 9 64 (by decide)
  have wd : current.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))):=
    (CallNormal.continuation_lookup_other source child "w" "wd" returned (by decide)).trans model.wdCell
  have buf : current.locals.lookup (ofString "buf")=some (.val (.word buffer)):=
    (CallNormal.continuation_lookup_other source child "w" "buf" returned (by decide)).trans model.bufferCell
  have p : current.locals.lookup (ofString "p")=some (.val (.word (buffer+9#64))):=
    (CallNormal.continuation_lookup_other source child "w" "p" returned (by decide)).trans model.positionCell
  have wCell : current.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 first))):=by rw [CallNormal.continuation_lookup_same,answer]
  have currentModel:=model.of_write firstFrame 9 wd buf p
  obtain ⟨encoded,positive,bounded,pair,tailFrame⟩:=currentModel.after_first_normal first firstPositive firstBound wCell value continued
  have total:=firstFrame.trans tailFrame
  refine ⟨encoded,positive,bounded,pair,?_⟩
  rw [endpoint]
  exact ⟨total.metadata,total.memory⟩

/-- The genuine p=buf+9 declaration and its lexical restoration add no
memory changes to the complete actual field/list writer frame. -/
theorem after_buffer_normal (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer buffer : BitVec 64) (start : Nat)
    (model : Writer input (bind source "p" (buffer+9#64)) pointer buffer start 9)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterBuffer=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤57 ∧ value=.rStruct [.val (.word buffer),.val (.word (BitVec.ofNat 64 encoded))] ∧ WriteFrame source target buffer 64 := by
  have buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)):=by
    simpa [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using model.bufferCell
  have read : eval source (.op .add [localVar "buf",.const 9#64])=some (.val (.word (buffer+9#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,buf,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [afterBuffer] at normal
  obtain ⟨inner,remaining,endpoint⟩:=declaration_return_word source target "p" _ (buffer+9#64) afterPointer value read normal
  obtain ⟨encoded,positive,bounded,pair,frame⟩:=model.after_pointer_normal value remaining
  refine ⟨encoded,positive,bounded,pair,?_⟩
  rw [endpoint]
  exact ⟨frame.metadata,frame.memory⟩

/-- A genuine current779 return derives the actual positive encoded pair,
its own allocated64-byte span, exact allocation metadata and protection of
all other memory. Only the input/heap entry is supplied in advance. -/
theorem body_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer heap : BitVec 64} {start : Nat} (entry : Entry input source pointer heap start)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤57 ∧ value=.rStruct [.val (.word heap),.val (.word (BitVec.ofNat 64 encoded))] ∧
      AllocatedBytes.Arena heap 64 ∧ MemoryMetadata.erase target=MemoryMetadata.erase (PersistentAlloc.post source heap 64#64) ∧
      ∀ query : BitVec 64,CopyGeneral.Away heap query 64→target.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 64#64]=some (PersistentAlloc.values 64#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  have noWrap : heap.toNat+(64#64 : BitVec 64).toNat+7<2^64:=by have upper:=entry.heapBound; change heap.toNat+64+7<2^64; omega
  rw [body_shape] at normal
  obtain ⟨room,funded,inner,remaining,endpoint⟩:=PersistentAlloc.call_normal_no_wrap source target "buf" [.const 64#64] afterBuffer heap 64#64 args
    (PersistentAlloc.original_code source.code entry.installed) (Trap.original_code source.code entry.installed) entry.heapCell noWrap value normal
  let current:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 64#64) "buf" heap
  let ready:=bind current "p" (heap+9#64)
  have owned : AllocatedBytes.Arena heap 64:=⟨entry.heapArena.lower,by change heap.toNat+64≤2952790016 at room; omega⟩
  have wd : ready.locals.lookup (ofString "wd")=some (.val (.word (pointer+BitVec.ofNat 64 start))):=
    (bind_lookup_other current "p" "wd" _ (by decide)).trans ((bind_lookup_other _ "buf" "wd" _ (by decide)).trans entry.wdCell)
  have buf : ready.locals.lookup (ofString "buf")=some (.val (.word heap)):=
    (bind_lookup_other current "p" "buf" _ (by decide)).trans (bind_lookup_same _ _ _)
  have model : Writer input ready pointer heap start 9:={
    installed:=entry.installed,domain:=entry.domain,bufferArena:=owned,bufferAligned:=entry.heapAligned,inputArena:=entry.inputArena,inputBefore:=entry.inputBefore
    heap:=Blob.HeapInput.of_fields source ready input pointer rfl rfl rfl entry.image,inside:=entry.inside,wdCell:=wd,bufferCell:=buf,positionCell:=bind_lookup_same _ _ _ }
  obtain ⟨encoded,positive,bounded,pair,frame⟩:=after_buffer_normal input current inner pointer heap start model value remaining
  refine ⟨encoded,positive,bounded,pair,owned,?_,?_⟩
  · rw [endpoint]
    exact frame.metadata
  · intro query away
    rw [endpoint]
    exact frame.memory query away

end Withdrawal

end InitECandidate.Solver.Input.CurrentRlp

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.short_body_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.twenty_normal_value

#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.body_shape
#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.execute

#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.FinishList.body_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.body_shape
#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.of_write
#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.scalar_read

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.word_call_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.word_call_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.advance_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.address_args
#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.address_call_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.address_call_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.finish_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.finish_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.advance_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.after_third_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.after_address_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.after_second_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.after_first_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.after_pointer_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.after_buffer_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.body_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.field_shape

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.field_never

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.fields_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.after_first_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.Writer.after_pointer_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.after_buffer_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.Withdrawal.body_normal
