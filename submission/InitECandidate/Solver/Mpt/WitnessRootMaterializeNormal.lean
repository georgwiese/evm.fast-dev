import InitECandidate.Solver.Mpt.WitnessRootPrefixNormal
import InitECandidate.Solver.Mpt.WitnessMaterializeRichNormal
import InitECandidate.Solver.Mpt.WitnessMaterializeEnvironment
import InitECandidate.Solver.Mpt.FailGuard

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessMaterialize

/-- Successful original lookup tails must pass the actual missing guard,
materialize the actual bounded database slice, and retain its closed graph
through the root cache/footer. All callee success is derived from this run. -/
theorem after_lookup_rich_normal_prefix (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap root : BitVec 64) (answer : Option Graph.Slice) (boundary : RootBoundary input source)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (rCell : source.locals.lookup (ofString "r")=some (MutableTable.NodeDb.output answer))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64) (rootArena : AllocatedBytes.Arena root 32)
    (hit : ∀ slice,answer=some slice → slice.2.toNat≤1024 ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤db.toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLookup=(some (.returned returned),post)) :
    RichOutput input heap.toNat db post returned ∧ WitnessCore.Stack.StablePrefix source post heap.toNat := by
  have safe : Input.LocalPrefix (ofString "db") missingGuard:=.ite _ (.call none _ _ (by simp)) .skip
  rw [lookup_tail_shape.1] at normal
  obtain ⟨middle,guardRun,continued,dbFrame⟩:=safe.normal_continue source post materializeCall returned normal
  obtain ⟨passed,same⟩:=Fail.guard_normal source middle missingTest [.const 1#64] installed guardRun
  subst middle
  cases answer with
  | none=>
    have rejected : eval source missingTest=some (.val (.word 1#64)):=by
      simp [eval,missingTest,localVar,evalHOLExact,toExact,rCell,MutableTable.NodeDb.output,MutableTable.NodeDb.triple,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using rejected.symm.trans passed
    exact ((by decide : (1#64 : BitVec 64)≠0#64) impossible).elim
  | some slice=>
    obtain ⟨small,lower,before⟩:=hit slice rfl
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) materializeArguments=
        some (WitnessMaterialize.values db slice.1 slice.2):=by
      simp [materializeArguments,WitnessMaterialize.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,rCell,
        MutableTable.NodeDb.output,MutableTable.NodeDb.triple]
    obtain ⟨callee,called,entryDb,entryPointer,entryLength⟩:=WitnessMaterialize.environment source.code.lookup db slice.1 slice.2
      (WitnessMaterialize.original_code source.code installed)
    rw [lookup_tail_shape.2] at continued
    obtain ⟨funded,target,childReturn,inner,childRun,checked,suffixRun,endpoint⟩:=Input.CallNormal.scoped_normal source post "nd" .one
      (ofString "_decode_witness_node") materializeArguments _ WitnessMaterialize.body afterMaterialize callee .one args called returned continued
    let entry:=callEntryStateHOLFinite source callee
    have entryBoundary:=boundary.erase_frame input source entry rfl (entryDb.trans dbCell.symm)
    have entryArena:=scratch.of_fields source entry 2713714688#64 2701135872#64 rfl rfl
    have childResult:=(WitnessMaterialize.rich_body_normal_prefix input entry target db slice.1 slice.2 heap 2713714688#64 2701135872#64
      entryBoundary entryDb entryPointer entryLength heapCell heapLower entryArena (by decide) before small lower installed childReturn childRun)
    have childOutput:=childResult.1
    have physical:=childOutput.1
    obtain ⟨nextHeap,node,childEq,childHeap,rest⟩:=physical
    let ready:=Input.CallNormal.continuationEntry source target "nd" childReturn
    have readyOutput : RichOutput input heap.toNat db ready (.val (.word node)):=by
      rw [←childEq]
      exact childOutput.of_erase input heap.toNat db target ready childReturn rfl
    have readyRoot : ready.locals.lookup (ofString "root_hash")=some (.val (.word root)):=
      (Input.CallNormal.continuation_lookup_other source target "nd" "root_hash" childReturn (by decide)).trans rootCell
    have readyNode : ready.locals.lookup (ofString "nd")=some (.val (.word node)):=
      (Input.CallNormal.continuation_lookup_same source target "nd" childReturn).trans (congrArg some childEq)
    have codeEq:=(Input.evaluation_fields entry target WitnessMaterialize.body (some (.returned childReturn)) childRun).2.2.2
    have readyInstalled : Input.OriginalCode.Installed ready.code:=by change Input.OriginalCode.Installed target.code; rw [codeEq]; exact installed
    have result:=suffix_rich_normal_prefix input ready inner heap.toNat db root node returned readyOutput heapLower readyRoot readyNode rootArena readyInstalled suffixRun
    refine ⟨result.2.1.of_erase input heap.toNat db inner post returned (by rw [endpoint]; rfl),?_⟩
    intro query lowerBound upperBound
    have endMemory : post.memory=inner.memory:=by rw [endpoint]; rfl
    exact (congrFun endMemory query).trans ((result.2.2 query lowerBound upperBound).trans (childResult.2.2 query lowerBound upperBound))

theorem after_lookup_rich_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap root : BitVec 64) (answer : Option Graph.Slice) (boundary : RootBoundary input source)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (rCell : source.locals.lookup (ofString "r")=some (MutableTable.NodeDb.output answer))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64) (rootArena : AllocatedBytes.Arena root 32)
    (hit : ∀ slice,answer=some slice → slice.2.toNat≤1024 ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤db.toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLookup=(some (.returned returned),post)) :
    RichOutput input heap.toNat db post returned :=
  (after_lookup_rich_normal_prefix input source post db heap root answer boundary installed dbCell rootCell rCell heapCell heapLower scratch rootArena hit returned normal).1

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.after_lookup_rich_normal

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.after_lookup_rich_normal_prefix
