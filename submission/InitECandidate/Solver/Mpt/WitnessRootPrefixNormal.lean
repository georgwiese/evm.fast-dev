import InitECandidate.Solver.Mpt.WitnessDecodeRootTrace
import InitECandidate.Solver.Mpt.WitnessRootSuffixNormal
import InitECandidate.Solver.MutableTable.WitnessDatabaseAnyNormal

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors Input.Main.WitnessConstructors

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

/-- A genuine original root lookup return exposes its actual bounded
witness answer and continuation, with both databases physically intact. -/
theorem lookup_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db root : BitVec 64) (boundary : RootBoundary input source) (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source lookupCall=(some (.returned value),post)) :
    ∃ current answer inner,Input.LocalEffects.erase current=Input.LocalEffects.erase source ∧
      current.locals.lookup (ofString "db")=some (.val (.word db)) ∧ current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      current.locals.lookup (ofString "r")=some (MutableTable.NodeDb.output answer) ∧
      (∀ slice,answer=some slice → ∃ index<nodeCount input,slice=nodeSlices input index ∧ slice.2.toNat≤1024 ∧
        AllocatedBytes.Arena slice.1 slice.2.toNat ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤db.toNat) ∧
      evaluateHOLFiniteState current afterLookup=(some (.returned value),inner) ∧ post=restore source "r" inner := by
  obtain ⟨codeArray,nodes,codes,heap,nodeData,codeData,nodeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩:=boundary
  have same : nodes=db:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nodeCell.symm.trans dbCell)))
  subst nodes
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) lookupArguments=
      some (MutableTable.NodeDb.arguments db root) := by
    simp [lookupArguments,MutableTable.NodeDb.arguments,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,rootCell]
  rw [shapes.2.2] at normal
  obtain ⟨target,answer,inner,pure,hit,continued,endpoint⟩:=nodeData.any_scoped_normal source post _ db (nodeCount input) 1024
    (nodeSlices input) 2713717584#64 root installed "r" lookupArguments afterLookup args value normal
  let current:=Input.CallNormal.continuationEntry source target "r" (MutableTable.NodeDb.output answer)
  exact ⟨current,answer,inner,(Input.CallNormal.continuation_erase source target "r" _).trans pure,
    (Input.CallNormal.continuation_lookup_other source target "r" "db" _ (by decide)).trans dbCell,
    (Input.CallNormal.continuation_lookup_other source target "r" "root_hash" _ (by decide)).trans rootCell,
    Input.CallNormal.continuation_lookup_same _ _ _ _,hit,continued,endpoint⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.prefix_normal
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.lookup_normal
