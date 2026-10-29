import InitECandidate.Solver.Mpt.WitnessDecodeRootTrace
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A genuine normal root-prefix execution either returns its actual empty
root or reaches the original database lookup. Both alternatives retain the
complete physical state of the real read-only comparison. -/
theorem current_lookup_normal_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db root emptyRoot : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (emptyCell : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    (value=.val (.word 0#64) ∧ LocalEffects.erase post=LocalEffects.erase source) ∨ ∃ current inner,
      LocalEffects.erase current=LocalEffects.erase source ∧
      current.locals.lookup (ofString "db")=some (.val (.word db)) ∧
      current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      evaluateHOLFiniteState current lookupCall=(some (.returned value),inner) ∧
      LocalEffects.erase post=LocalEffects.erase inner := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compareArguments=
      some (MutableTable.MemeqByteRuntime.values root emptyRoot 32) := by
    simp [compareArguments,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,rootCell,emptyCell,MutableTable.MemeqByteRuntime.values]
  obtain ⟨callee,called,aCell,bCell,nCell⟩:=MutableTable.MemeqByteRuntime.environment source.code.lookup root emptyRoot 32
    (MutableTable.MemeqAny.original_code source.code installed)
  rw [shapes.1] at normal
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "is_empty" .one
    (ofString "memeq") compareArguments _ Memeq32.body afterCompare callee .one args called value normal
  have frame:=MutableTable.MemeqAny.readonly source.code (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at frame
  change LocalEffects.erase target=LocalEffects.erase source at frame
  cases answer with
  | rStruct fields=>simp [shapeOfHOLExact,shapeEqHOL] at checked
  | nStruct label fields=>simp [shapeOfHOLExact,shapeEqHOL] at checked
  | val word=>
    cases word with
    | word flag=>
      let current:=CallNormal.continuationEntry source target "is_empty" (.val (.word flag))
      have currentFrame : LocalEffects.erase current=LocalEffects.erase source:=frame
      have flagCell : current.locals.lookup (ofString "is_empty")=some (.val (.word flag)):=CallNormal.continuation_lookup_same _ _ _ _
      have guardRun : evaluateHOLFiniteState current emptyGuard=
          (if flag=0#64 then (none,current) else (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite current)) := by
        simp [emptyGuard,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,flagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
          evaluateHOLFiniteState_skip,evaluateHOLFiniteState_return,shapeOfHOLExact,sizeOfShapeWithContextHOL]
      change evaluateHOLFiniteState current afterCompare=(some (.returned value),inner) at continued
      rw [shapes.2.1,evaluateHOLFiniteState_seq_line780,guardRun] at continued
      by_cases zero : flag=0#64
      · rw [if_pos zero] at continued
        exact Or.inr ⟨current,inner,currentFrame,
          (CallNormal.continuation_lookup_other source target "is_empty" "db" _ (by decide)).trans dbCell,
          (CallNormal.continuation_lookup_other source target "is_empty" "root_hash" _ (by decide)).trans rootCell,
          continued,by rw [endpoint]; rfl⟩
      · rw [if_neg zero] at continued
        have observed:=congrArg Prod.fst continued
        have valueEq : value=.val (.word 0#64):=by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using observed.symm
        have innerEq : inner=emptyLocalsHOLFinite current:=(congrArg Prod.snd continued).symm
        exact Or.inl ⟨valueEq,by rw [endpoint,innerEq]; exact currentFrame⟩

/-- No typed empty-root global is an entry assumption: a missing or
nonscalar operand cannot produce the observed normal return. -/
theorem current_lookup_normal_trace_any (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db root : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    (value=.val (.word 0#64) ∧ LocalEffects.erase post=LocalEffects.erase source) ∨ ∃ current inner,
      LocalEffects.erase current=LocalEffects.erase source ∧
      current.locals.lookup (ofString "db")=some (.val (.word db)) ∧
      current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      evaluateHOLFiniteState current lookupCall=(some (.returned value),inner) ∧
      LocalEffects.erase post=LocalEffects.erase inner := by
  classical
  cases emptyRead : source.globals.lookup (ofString "empty_trie_root") with
  | none=>
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compareArguments=none := by
      simp [compareArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rootCell,emptyRead]
    rw [shapes.1,evaluateHOLFiniteState_decCall_fixClockRewrite,args] at normal
    cases normal
  | some answer=>
    cases answer with
    | val word=>
      cases word with
      | word emptyRoot=>exact current_lookup_normal_trace source post db root emptyRoot installed dbCell rootCell emptyRead value normal
    | rStruct fields=>
      let values : List (ValueHOL 64):=[.val (.word root),.rStruct fields,.val (.word 32#64)]
      have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compareArguments=some values := by
        simp [compareArguments,values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rootCell,emptyRead]
      have failed : lookupCodeHOLFinite source.code.lookup (ofString "memeq") values=none := by
        apply (lookupCodeHOLFinite_eq_none_iff source.code.lookup (ofString "memeq") values).mpr
        unfold lookupCodeHOLExact
        rw [MutableTable.MemeqAny.original_code source.code installed]
        simp [values,Memeq32.formals,shapeOfHOLExact,shapeEqHOL]
      rw [shapes.1,evaluateHOLFiniteState_decCall_fixClockRewrite,args] at normal
      simp only [failed] at normal
      cases normal
    | nStruct label fields=>
      let values : List (ValueHOL 64):=[.val (.word root),.nStruct label fields,.val (.word 32#64)]
      have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compareArguments=some values := by
        simp [compareArguments,values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rootCell,emptyRead]
      have failed : lookupCodeHOLFinite source.code.lookup (ofString "memeq") values=none := by
        apply (lookupCodeHOLFinite_eq_none_iff source.code.lookup (ofString "memeq") values).mpr
        unfold lookupCodeHOLExact
        rw [MutableTable.MemeqAny.original_code source.code installed]
        simp [values,Memeq32.formals,shapeOfHOLExact,shapeEqHOL]
      rw [shapes.1,evaluateHOLFiniteState_decCall_fixClockRewrite,args] at normal
      simp only [failed] at normal
      cases normal

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.current_lookup_normal_trace
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.current_lookup_normal_trace_any
