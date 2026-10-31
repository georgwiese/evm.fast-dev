import InitECandidate.Solver.Input.CurrentRlp.HeaderWrite
import InitECandidate.Solver.Input.RlpWrite.ListWrite
import InitECandidate.Solver.Input.TailCallNormal
import InitECandidate.Solver.Input.RlpLength.ScalarSizes
import InitECandidate.Solver.Input.CurrentRlp.WriteFrame
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpWrite

/-- A real short form writes its single tag and returns1. -/
theorem short_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (tag : ExpHOL 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (shortForm tag)=(some (.returned value),target)) :
    value=.val (.word 1#64) ∧ WriteFrame source target dst 1 := by
  rw [shortForm] at normal
  obtain ⟨middle,stored,returned⟩:=sequence_returned source target _ _ value (byte_store_local (ofString "n") _ _ source).2.1 normal
  have readD : eval source (localVar "dst")=some (.val (.word (dst+0#64))):=by
    simpa only [eval,evalHOLExact,toExact,localVar,BitVec.add_zero] using d
  have first:=WriteFrame.byte source middle dst 0#64 1 (by decide) _ _ readD stored
  obtain ⟨read,endpoint⟩:=return_normal middle target (.const 1#64) value returned
  have answer : value=.val (.word 1#64):=Option.some.inj read.symm
  have last : WriteFrame middle target dst 1:=by rw [endpoint]; exact ⟨rfl,by intros; rfl⟩
  exact ⟨answer,first.trans last⟩


theorem short_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (tag : ExpHOL 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (shortForm tag)=(some (.returned value),target)) :
    value=.val (.word 1#64) ∧ WriteFrame source target dst 9 := by
  obtain ⟨answer,frame⟩:=short_normal_exact source target dst tag d value normal
  exact ⟨answer,frame.weaken (by decide)⟩

/-- The actual tag and ignored reverse-byte caller stay inside nine bytes.
Each local/metadata fact is transported from that same real normal store. -/
theorem length_tail_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64) (count : Nat)
    (parameter : String) (tag : ExpHOL 64) (bounded : count≤8) (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word word)))
    (ll : source.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (lengthTail parameter tag)=(some (.returned value),target)) :
    value=.val (.word (BitVec.ofNat 64 (count+1))) ∧ WriteFrame source target dst (count+1) := by
  rw [lengthTail] at normal
  obtain ⟨middle,stored,remaining⟩:=sequence_returned source target _ _ value (byte_store_local (ofString "n") _ _ source).2.1 normal
  have readD : eval source (localVar "dst")=some (.val (.word dst)):=by simpa only [eval,evalHOLExact,toExact,localVar] using d
  have storeFrame:=byte_store_normal_frame source middle (localVar "dst") tag dst readD stored
  have first:=WriteFrame.byte source middle dst 0#64 (count+1) (by change 0<count+1; omega) _ _ (by simpa only [BitVec.add_zero] using readD) stored
  have middleD : middle.locals.lookup (ofString "dst")=some (.val (.word dst)):=by rw [storeFrame.1]; exact d
  have middleV : middle.locals.lookup (ofString parameter)=some (.val (.word word)):=by rw [storeFrame.1]; exact v
  have middleLl : middle.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=by rw [storeFrame.1]; exact ll
  have middleInstalled : OriginalCode.Installed middle.code:=by rw [storeFrame.1]; exact installed
  let arguments : List (ExpHOL 64):=[.op .add [localVar "dst",.const 1#64],localVar parameter,localVar "ll"]
  have args : evalListHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) arguments=
      some [.val (.word (dst+1#64)),.val (.word word),.val (.word (BitVec.ofNat 64 count))]:=by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,middleD,middleV,middleLl,valueIsWord,valueWord,wordOpHOL,wordOp]
  have never:=(LocalPrefix.call (key:=ofString "n") none (ofString "rlp_put_be") arguments (by intro name impossible; cases impossible)).summary_full middle |>.2.1
  obtain ⟨last,called,returned⟩:=sequence_returned middle target _ _ value never remaining
  have second:=(CurrentRlp.PutBe.call_frame middle last arguments (dst+1#64) word count (by omega) middleInstalled args called).shift dst 1 count (count+1) (by omega)
  obtain ⟨read,endpoint⟩:=return_normal last target (.op .add [.const 1#64,localVar "ll"]) value returned
  have lastLl : last.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=
    (CallNormal.ignored_lookup middle last (ofString "ll") (ofString "rlp_put_be") arguments called).trans middleLl
  have expected : eval last (.op .add [.const 1#64,localVar "ll"])=some (.val (.word (BitVec.ofNat 64 (count+1)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,lastLl,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add,BitVec.add_comm]
  have answer : value=.val (.word (BitVec.ofNat 64 (count+1))):=Option.some.inj (read.symm.trans expected)
  have finalFrame : WriteFrame last target dst (count+1):=by rw [endpoint]; exact ⟨rfl,by intros; rfl⟩
  exact ⟨answer,(first.trans second).trans finalFrame⟩


theorem length_tail_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64) (count : Nat)
    (parameter : String) (tag : ExpHOL 64) (bounded : count≤8) (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word word)))
    (ll : source.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (lengthTail parameter tag)=(some (.returned value),target)) :
    value=.val (.word (BitVec.ofNat 64 (count+1))) ∧ WriteFrame source target dst 9 := by
  obtain ⟨answer,frame⟩:=length_tail_normal_exact source target dst word count parameter tag bounded installed d v ll value normal
  exact ⟨answer,frame.weaken (by omega)⟩

/-- An actual length-helper return supplies the long form's true count,
restored caller metadata and bounded write frame, without predicting success. -/
theorem long_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (parameter : String) (tag : ExpHOL 64) (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word word)))
    (dstNe : ofString "ll"≠ofString "dst") (parameterNe : ofString "ll"≠ofString parameter)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (longForm parameter tag)=(some (.returned value),target)) :
    ∃ encoded,encoded=RlpLength.Be.byteCount 8 word+1 ∧ 1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧ WriteFrame source target dst encoded := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar parameter]=some [.val (.word word)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,v]
  obtain ⟨callee,called,cell⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_be_len") "v" BeLength.body word (BeLength.original_code source.code installed)
  rw [longForm] at normal
  obtain ⟨funded,built,returned,inner,bodyRun,checked,tailRun,endpoint⟩:=CallNormal.scoped_normal source target "ll" .one (ofString "rlp_be_len") [localVar parameter]
    [.val (.word word)] BeLength.body (lengthTail parameter tag) callee .one args called value normal
  obtain ⟨count,exactCount,bounded,answer,price,metadata⟩:=BeLength.body_normal_exact (callEntryStateHOLFinite source callee) built word cell returned bodyRun
  let ready:=CallNormal.continuationEntry source built "ll" returned
  have pure : LocalEffects.erase ready=LocalEffects.erase source:=metadata
  have readyInstalled : OriginalCode.Installed ready.code:=by rw [LocalEffects.code_of_erase source ready pure]; exact installed
  have readyD : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (CallNormal.continuation_lookup_other source built "ll" "dst" returned dstNe).trans d
  have readyV : ready.locals.lookup (ofString parameter)=some (.val (.word word)):=
    (CallNormal.continuation_lookup_other source built "ll" parameter returned parameterNe).trans v
  have readyLl : ready.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=by rw [CallNormal.continuation_lookup_same,answer]
  obtain ⟨valueEq,tailFrame⟩:=length_tail_normal_exact ready inner dst word count parameter tag bounded readyInstalled readyD readyV readyLl value tailRun
  have total:=(WriteFrame.readonly dst (count+1) pure).trans tailFrame
  refine ⟨count+1,by rw [exactCount],by omega,by omega,valueEq,?_⟩
  rw [endpoint]
  exact ⟨total.metadata,total.memory⟩


theorem long_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (parameter : String) (tag : ExpHOL 64) (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word word)))
    (dstNe : ofString "ll"≠ofString "dst") (parameterNe : ofString "ll"≠ofString parameter)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (longForm parameter tag)=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧ WriteFrame source target dst 9 := by
  obtain ⟨encoded,_exactCount,lower,upper,answer,frame⟩:=long_normal_exact source target dst word parameter tag installed d v dstNe parameterNe value normal
  exact ⟨encoded,lower,upper,answer,frame.weaken upper⟩

/-- Every true current header-writer return supplies its real1..9-byte
answer, full metadata preservation, bounded writes and all-outcome cost. -/
theorem body_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word word)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,encoded=RlpLength.Header.encodedLength word ∧ 1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-target.clock≤18 ∧ WriteFrame source target dst encoded := by
  have priced:=body_cost source dst word installed d n
  rw [normal] at priced
  have testRead : eval source RlpWrite.HeaderWrite.condition=some (.val (.word (if word.toNat≤55 then 1#64 else 0#64))):=by
    simp [eval,RlpWrite.HeaderWrite.condition,evalHOLExact,toExact,localVar,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def]
  simp only [eval] at testRead
  by_cases short : word.toNat≤55
  · have guard : evaluateHOLFiniteState source (.ite RlpWrite.HeaderWrite.condition (shortForm RlpWrite.HeaderWrite.shortTag) .skip)=
        evaluateHOLFiniteState source (shortForm RlpWrite.HeaderWrite.shortTag):=by
      rw [evaluateHOLFiniteState_ite,testRead]
      simp [short]
    have same : evaluateHOLFiniteState source body=evaluateHOLFiniteState source (shortForm RlpWrite.HeaderWrite.shortTag):=by
      rw [current_body,RlpWrite.HeaderWrite.body_shape,evaluateHOLFiniteState_seq_line780,guard]
      have stops:=short_stops source RlpWrite.HeaderWrite.shortTag
      generalize computed : evaluateHOLFiniteState source (shortForm RlpWrite.HeaderWrite.shortTag)=output at stops ⊢
      obtain ⟨result,post⟩:=output
      cases result with
      | none=>exact (stops rfl).elim
      | some result=>rfl
    obtain ⟨answer,frame⟩:=short_normal_exact source target dst _ d value (same.symm.trans normal)
    exact ⟨1,by simp only [RlpLength.Header.encodedLength,if_pos short],by decide,by decide,answer,priced,frame⟩
  · have guard : evaluateHOLFiniteState source (.ite RlpWrite.HeaderWrite.condition (shortForm RlpWrite.HeaderWrite.shortTag) .skip)=(none,source):=by
      rw [evaluateHOLFiniteState_ite,testRead]
      simp [short,evaluateHOLFiniteState_skip]
    have same : evaluateHOLFiniteState source body=evaluateHOLFiniteState source (longForm "n" RlpWrite.HeaderWrite.longTag):=by
      rw [current_body,RlpWrite.HeaderWrite.body_shape]
      exact StateSteps.next_sequence source source _ _ guard (Nat.le_refl _)
    obtain ⟨encoded,exactCount,lower,upper,answer,frame⟩:=long_normal_exact source target dst word "n" RlpWrite.HeaderWrite.longTag installed d n (by decide) (by decide) value (same.symm.trans normal)
    exact ⟨encoded,by simpa only [RlpLength.Header.encodedLength,if_neg short] using exactCount,lower,upper,answer,priced,frame⟩



theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word word)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-target.clock≤18 ∧ WriteFrame source target dst 9 := by
  obtain ⟨encoded,_exactCount,lower,upper,answer,price,frame⟩:=body_normal_exact source target dst word installed d n value normal
  exact ⟨encoded,lower,upper,answer,price,frame.weaken upper⟩

/-- Shared real short-tag guard. A false guard leaves precisely the same
source for its observed tail; a true guard cannot fall through its return. -/
theorem guarded_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (test tag : ExpHOL 64) (rest : ProgHOL 64) (condition : Prop) [Decidable condition]
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (read : eval source test=some (.val (.word (if condition then 1#64 else 0#64)))) (value : ValueHOL 64)
    (back : evaluateHOLFiniteState source rest=(some (.returned value),target)→
      ∃ encoded,1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧ WriteFrame source target dst 9)
    (normal : evaluateHOLFiniteState source (.seq (.ite test (shortForm tag) .skip) rest)=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧ WriteFrame source target dst 9 := by
  simp only [eval] at read
  by_cases active : condition
  · have guard : evaluateHOLFiniteState source (.ite test (shortForm tag) .skip)=evaluateHOLFiniteState source (shortForm tag):=by
      rw [evaluateHOLFiniteState_ite,read]
      simp [active]
    have same : evaluateHOLFiniteState source (.seq (.ite test (shortForm tag) .skip) rest)=evaluateHOLFiniteState source (shortForm tag):=by
      rw [evaluateHOLFiniteState_seq_line780,guard]
      have stops:=short_stops source tag
      generalize computed : evaluateHOLFiniteState source (shortForm tag)=output at stops ⊢
      obtain ⟨result,post⟩:=output
      cases result with
      | none=>exact (stops rfl).elim
      | some result=>rfl
    obtain ⟨answer,frame⟩:=short_normal source target dst tag d value (same.symm.trans normal)
    exact ⟨1,by decide,by decide,answer,frame⟩
  · have guard : evaluateHOLFiniteState source (.ite test (shortForm tag) .skip)=(none,source):=by
      rw [evaluateHOLFiniteState_ite,read]
      simp [active,evaluateHOLFiniteState_skip]
    have same:=StateSteps.next_sequence source source (.ite test (shortForm tag) .skip) rest guard (Nat.le_refl _)
    exact back (same.symm.trans normal)

end InitECandidate.Solver.Input.CurrentRlp.HeaderWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.short_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.length_tail_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.long_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.body_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.guarded_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.short_normal_exact
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.length_tail_normal_exact
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.long_normal_exact
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.body_normal_exact

namespace InitECandidate.Solver.Input.CurrentRlp.ListWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

abbrev body:=Code.body .writeList

theorem current_body : body=RlpWrite.ListWrite.body:=rfl

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_encode_list_header")=some (RlpWrite.ListWrite.formals,body,.one) := by
  apply Code.installed_as code installed .writeList
  simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_rlp_encode_list_header,RlpWrite.ListWrite.formals,body,Code.body,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst payload : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "payload_len")=some (.val (.word payload))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤19 := by
  obtain ⟨callee,called,dCell,_baseCell,nCell⟩:=RlpWrite.HeaderWrite.environment source.code.lookup dst 192#64 payload (HeaderWrite.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) RlpWrite.ListWrite.arguments=
      some [.val (.word dst),.val (.word 192#64),.val (.word payload)]:=by
    simp [RlpWrite.ListWrite.arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,d,n]
  rw [current_body,RlpWrite.ListWrite.body_shape]
  exact ClockCost.call_current source none (ofString "rlp_write_header") RlpWrite.ListWrite.arguments _ HeaderWrite.body callee .one 18 args called
    (HeaderWrite.body_cost (callEntryStateHOLFinite source callee) dst payload installed dCell nCell)

/-- A real list-header return agrees with the earlier size helper and
writes exactly that header span, with no output-room premise. -/
theorem body_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst payload : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "payload_len")=some (.val (.word payload)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,encoded=RlpLength.Header.encodedLength payload ∧ 1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-target.clock≤19 ∧ WriteFrame source target dst encoded := by
  obtain ⟨callee,called,dCell,_baseCell,nCell⟩:=RlpWrite.HeaderWrite.environment source.code.lookup dst 192#64 payload (HeaderWrite.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) RlpWrite.ListWrite.arguments=
      some [.val (.word dst),.val (.word 192#64),.val (.word payload)]:=by
    simp [RlpWrite.ListWrite.arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,d,n]
  have shaped:=normal
  rw [current_body,RlpWrite.ListWrite.body_shape] at shaped
  obtain ⟨_funded,built,run,_checked,endpoint⟩:=CallNormal.tail_callee_return source target (ofString "rlp_write_header") RlpWrite.ListWrite.arguments
    [.val (.word dst),.val (.word 192#64),.val (.word payload)] HeaderWrite.body callee .one args called value shaped
  obtain ⟨encoded,exactCount,lower,upper,answer,_price,frame⟩:=HeaderWrite.body_normal_exact (callEntryStateHOLFinite source callee) built dst payload installed dCell nCell value run
  have price:=body_cost source dst payload installed d n
  rw [normal] at price
  refine ⟨encoded,exactCount,lower,upper,answer,price,?_⟩
  rw [endpoint]
  exact ⟨frame.metadata,frame.memory⟩

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (dst payload : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word dst),.val (.word payload)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_encode_list_header") arguments)).2.clock≤20 := by
  obtain ⟨callee,called,dCell,nCell⟩:=RlpWrite.ListWrite.environment source.code.lookup dst payload (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "rlp_encode_list_header") arguments _ body callee .one 19 args called
    (body_cost (callEntryStateHOLFinite source callee) dst payload installed dCell nCell)

/-- The actual ignored caller retains the exact header span and every
nonmemory field, without assuming its allocator or stores will succeed. -/
theorem call_frame_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (dst payload : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word dst),.val (.word payload)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_encode_list_header") arguments)=(none,target)) :
    WriteFrame source target dst (RlpLength.Header.encodedLength payload) := by
  obtain ⟨callee,called,dCell,nCell⟩:=RlpWrite.ListWrite.environment source.code.lookup dst payload (original_code source.code installed)
  apply WriteFrame.ignored source target (ofString "rlp_encode_list_header") arguments _ body callee .one dst (RlpLength.Header.encodedLength payload) args called
  · intro post returned run
    obtain ⟨encoded,exactCount,_lower,_upper,_answer,_price,frame⟩:=body_normal_exact (callEntryStateHOLFinite source callee) post dst payload installed dCell nCell returned run
    simpa only [exactCount] using frame
  · exact normal

end InitECandidate.Solver.Input.CurrentRlp.ListWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.ListWrite.current_body
#print axioms InitECandidate.Solver.Input.CurrentRlp.ListWrite.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.ListWrite.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.ListWrite.body_normal_exact
#print axioms InitECandidate.Solver.Input.CurrentRlp.ListWrite.call_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.ListWrite.call_frame_exact
