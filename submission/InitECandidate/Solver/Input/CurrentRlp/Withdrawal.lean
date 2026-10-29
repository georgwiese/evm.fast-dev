import InitECandidate.Solver.Input.CurrentRlp.BytesWrite
import InitECandidate.Solver.Input.NoReturnAtoms

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

end InitECandidate.Solver.Input.CurrentRlp

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderWrite.short_body_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.twenty_normal_value
