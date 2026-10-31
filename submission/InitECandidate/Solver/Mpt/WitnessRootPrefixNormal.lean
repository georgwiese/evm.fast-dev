import InitECandidate.Solver.Mpt.WitnessDecodeRootTrace
import InitECandidate.Solver.Mpt.WitnessRootSuffixNormal
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Call

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch


/-- Normal returns of the actual comparison scope are either its literal
null return or a genuine lookup continuation. No cost-only stopping
alternative is used to assert successful reachability. -/
theorem prefix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db root emptyRoot : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (emptyCell : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    (value=.val (.word 0#64) ∧ Input.LocalEffects.erase post=Input.LocalEffects.erase source) ∨
    ∃ current inner,Input.LocalEffects.erase current=Input.LocalEffects.erase source ∧
      current.locals.lookup (ofString "db")=some (.val (.word db)) ∧ current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      evaluateHOLFiniteState current lookupCall=(some (.returned value),inner) ∧ post=restore source "is_empty" inner := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compareArguments=
      some (MutableTable.MemeqByteRuntime.values root emptyRoot 32) := by
    simp [compareArguments,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,rootCell,emptyCell,MutableTable.MemeqByteRuntime.values]
  obtain ⟨callee,called,aCell,bCell,nCell⟩:=MutableTable.MemeqByteRuntime.environment source.code.lookup root emptyRoot 32
    (MutableTable.MemeqAny.original_code source.code installed)
  rw [shapes.1] at normal
  obtain ⟨funded,target,returned,inner,bodyRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post "is_empty" .one (ofString "memeq")
    compareArguments _ Memeq32.body afterCompare callee .one args called value normal
  have pure:=MutableTable.MemeqAny.readonly source.code (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at pure
  let current:=Input.CallNormal.continuationEntry source target "is_empty" returned
  have currentPure : Input.LocalEffects.erase current=Input.LocalEffects.erase source:=
    (Input.CallNormal.continuation_erase source target "is_empty" returned).trans pure
  have currentDb : current.locals.lookup (ofString "db")=some (.val (.word db)):=
    (Input.CallNormal.continuation_lookup_other source target "is_empty" "db" returned (by decide)).trans dbCell
  have currentRoot : current.locals.lookup (ofString "root_hash")=some (.val (.word root)):=
    (Input.CallNormal.continuation_lookup_other source target "is_empty" "root_hash" returned (by decide)).trans rootCell
  cases returned with
  | rStruct fields=>simp [shapeOfHOLExact,shapeEqHOL] at checked
  | nStruct name fields=>simp [shapeOfHOLExact,shapeEqHOL] at checked
  | val payload=>
    cases payload with
    | word flag=>
      have flagCell : current.locals.lookup (ofString "is_empty")=some (.val (.word flag)):=bind_lookup_same _ _ _
      have choice : evaluateHOLFiniteState current emptyGuard=
          if flag=0#64 then (none,current) else evaluateHOLFiniteState current (.return (.const 0#64)) := by
        rw [emptyGuard,evaluateHOLFiniteState_ite]
        by_cases zero : flag=0#64 <;>
          simp [evalHOLExact,localVar,toExact,flagCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
      rw [shapes.2.1,evaluateHOLFiniteState_seq_line780,choice] at continued
      by_cases zero : flag=0#64
      · rw [if_pos zero] at continued
        exact Or.inr ⟨current,inner,currentPure,currentDb,currentRoot,continued,endpoint⟩
      · rw [if_neg zero] at continued
        have literal : evaluateHOLFiniteState current (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite current):=by
          simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,valueIsWord,shapeOfHOLExact,isWfShapeExactHOL]
        rw [literal] at continued
        have valueEq : value=.val (.word 0#64):=by simpa using (congrArg Prod.fst continued).symm
        have innerEq : inner=emptyLocalsHOLFinite current:=(congrArg Prod.snd continued).symm
        refine Or.inl ⟨valueEq,?_⟩
        have frame : Input.LocalEffects.erase post=Input.LocalEffects.erase current:=by rw [endpoint,innerEq]; rfl
        exact frame.trans currentPure

/-- A real normal Patricia lookup returns its genuine value-set member
and readonly callee state. No future materializer success is assumed. -/
theorem lookup_normal (data : Input.CurrentTable.NodeBuild.Data)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (database : Input.CurrentTable.NodeLookup.Database source data) (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source lookupCall=(some (.returned value),post)) :
    ∃ current answer inner,Input.LocalEffects.erase current=Input.LocalEffects.erase source ∧
      current.locals.lookup (ofString "db")=some (.val (.word data.table)) ∧ current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      current.locals.lookup (ofString "r")=some answer ∧ Input.CurrentTable.NodeLookup.Result data answer ∧
      evaluateHOLFiniteState current afterLookup=(some (.returned value),inner) ∧ post=restore source "r" inner := by
  obtain ⟨imageRoot,next,count,valid,bits,left,right,keys,image,bounded⟩:=database.image
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) lookupArguments=
      some [.val (.word data.table),.val (.word root)] := by
    simp [lookupArguments,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,rootCell]
  rw [shapes.2.2] at normal
  obtain ⟨target,answer,inner,result,pure,forward,price,continued,endpoint⟩:=Input.CurrentTable.NodeLookup.scoped_returned data source post
    data.table data.cap imageRoot root next count valid bits left right keys image database.rows installed "r" lookupArguments afterLookup args value normal
  let current:=Input.CallNormal.continuationEntry source target "r" answer
  exact ⟨current,answer,inner,pure,
    (Input.CallNormal.continuation_lookup_other source target "r" "db" answer (by decide)).trans dbCell,
    (Input.CallNormal.continuation_lookup_other source target "r" "root_hash" answer (by decide)).trans rootCell,
    Input.CallNormal.continuation_lookup_same _ _ _ _,result,continued,endpoint⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.prefix_normal
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.lookup_normal
