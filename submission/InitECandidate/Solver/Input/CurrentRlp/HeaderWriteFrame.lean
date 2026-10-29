import InitECandidate.Solver.Input.CurrentRlp.HeaderWrite
import InitECandidate.Solver.Input.CurrentRlp.WriteFrame
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpWrite

/-- A real short form writes its single tag and returns1. -/
theorem short_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (tag : ExpHOL 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (shortForm tag)=(some (.returned value),target)) :
    value=.val (.word 1#64) ∧ WriteFrame source target dst 9 := by
  rw [shortForm] at normal
  obtain ⟨middle,stored,returned⟩:=sequence_returned source target _ _ value (byte_store_local (ofString "n") _ _ source).2.1 normal
  have readD : eval source (localVar "dst")=some (.val (.word (dst+0#64))):=by
    simpa only [eval,evalHOLExact,toExact,localVar,BitVec.add_zero] using d
  have first:=WriteFrame.byte source middle dst 0#64 9 (by decide) _ _ readD stored
  obtain ⟨read,endpoint⟩:=return_normal middle target (.const 1#64) value returned
  have answer : value=.val (.word 1#64):=Option.some.inj read.symm
  have last : WriteFrame middle target dst 9:=by rw [endpoint]; exact ⟨rfl,by intros; rfl⟩
  exact ⟨answer,first.trans last⟩

/-- The actual tag and ignored reverse-byte caller stay inside nine bytes.
Each local/metadata fact is transported from that same real normal store. -/
theorem length_tail_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64) (count : Nat)
    (parameter : String) (tag : ExpHOL 64) (bounded : count≤8) (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word word)))
    (ll : source.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (lengthTail parameter tag)=(some (.returned value),target)) :
    value=.val (.word (BitVec.ofNat 64 (count+1))) ∧ WriteFrame source target dst 9 := by
  rw [lengthTail] at normal
  obtain ⟨middle,stored,remaining⟩:=sequence_returned source target _ _ value (byte_store_local (ofString "n") _ _ source).2.1 normal
  have readD : eval source (localVar "dst")=some (.val (.word dst)):=by simpa only [eval,evalHOLExact,toExact,localVar] using d
  have storeFrame:=byte_store_normal_frame source middle (localVar "dst") tag dst readD stored
  have first:=WriteFrame.byte source middle dst 0#64 9 (by decide) _ _ (by simpa only [BitVec.add_zero] using readD) stored
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
  have second:=(CurrentRlp.PutBe.call_frame middle last arguments (dst+1#64) word count (by omega) middleInstalled args called).shift dst 1 count 9 (by omega)
  obtain ⟨read,endpoint⟩:=return_normal last target (.op .add [.const 1#64,localVar "ll"]) value returned
  have lastLl : last.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=
    (CallNormal.ignored_lookup middle last (ofString "ll") (ofString "rlp_put_be") arguments called).trans middleLl
  have expected : eval last (.op .add [.const 1#64,localVar "ll"])=some (.val (.word (BitVec.ofNat 64 (count+1)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,lastLl,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add,BitVec.add_comm]
  have answer : value=.val (.word (BitVec.ofNat 64 (count+1))):=Option.some.inj (read.symm.trans expected)
  have finalFrame : WriteFrame last target dst 9:=by rw [endpoint]; exact ⟨rfl,by intros; rfl⟩
  exact ⟨answer,(first.trans second).trans finalFrame⟩

/-- An actual length-helper return supplies the long form's true count,
restored caller metadata and bounded write frame, without predicting success. -/
theorem long_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (parameter : String) (tag : ExpHOL 64) (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word word)))
    (dstNe : ofString "ll"≠ofString "dst") (parameterNe : ofString "ll"≠ofString parameter)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (longForm parameter tag)=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧ WriteFrame source target dst 9 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar parameter]=some [.val (.word word)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,v]
  obtain ⟨callee,called,cell⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_be_len") "v" BeLength.body word (BeLength.original_code source.code installed)
  rw [longForm] at normal
  obtain ⟨funded,built,returned,inner,bodyRun,checked,tailRun,endpoint⟩:=CallNormal.scoped_normal source target "ll" .one (ofString "rlp_be_len") [localVar parameter]
    [.val (.word word)] BeLength.body (lengthTail parameter tag) callee .one args called value normal
  obtain ⟨count,bounded,answer,price,metadata⟩:=BeLength.body_normal (callEntryStateHOLFinite source callee) built word cell returned bodyRun
  let ready:=CallNormal.continuationEntry source built "ll" returned
  have pure : LocalEffects.erase ready=LocalEffects.erase source:=metadata
  have readyInstalled : OriginalCode.Installed ready.code:=by rw [LocalEffects.code_of_erase source ready pure]; exact installed
  have readyD : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (CallNormal.continuation_lookup_other source built "ll" "dst" returned dstNe).trans d
  have readyV : ready.locals.lookup (ofString parameter)=some (.val (.word word)):=
    (CallNormal.continuation_lookup_other source built "ll" parameter returned parameterNe).trans v
  have readyLl : ready.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=by rw [CallNormal.continuation_lookup_same,answer]
  obtain ⟨valueEq,tailFrame⟩:=length_tail_normal ready inner dst word count parameter tag bounded readyInstalled readyD readyV readyLl value tailRun
  have total:=(WriteFrame.readonly dst 9 pure).trans tailFrame
  refine ⟨count+1,by omega,by omega,valueEq,?_⟩
  rw [endpoint]
  exact ⟨total.metadata,total.memory⟩

/-- Every true current header-writer return supplies its real1..9-byte
answer, full metadata preservation, bounded writes and all-outcome cost. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word word)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-target.clock≤18 ∧ WriteFrame source target dst 9 := by
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
    obtain ⟨answer,frame⟩:=short_normal source target dst _ d value (same.symm.trans normal)
    exact ⟨1,by decide,by decide,answer,priced,frame⟩
  · have guard : evaluateHOLFiniteState source (.ite RlpWrite.HeaderWrite.condition (shortForm RlpWrite.HeaderWrite.shortTag) .skip)=(none,source):=by
      rw [evaluateHOLFiniteState_ite,testRead]
      simp [short,evaluateHOLFiniteState_skip]
    have same : evaluateHOLFiniteState source body=evaluateHOLFiniteState source (longForm "n" RlpWrite.HeaderWrite.longTag):=by
      rw [current_body,RlpWrite.HeaderWrite.body_shape]
      exact StateSteps.next_sequence source source _ _ guard (Nat.le_refl _)
    obtain ⟨encoded,lower,upper,answer,frame⟩:=long_normal source target dst word "n" RlpWrite.HeaderWrite.longTag installed d n (by decide) (by decide) value (same.symm.trans normal)
    exact ⟨encoded,lower,upper,answer,priced,frame⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.short_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.length_tail_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.long_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.body_normal
