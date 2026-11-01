import InitECandidate.Solver.Mpt.WitnessRootMaterializeNormal
import InitECandidate.Solver.Mpt.WitnessMaterializeRichNormal

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessMaterialize WitnessCore WitnessCore.Stack

/-- The actual root cache allocation and copy preserve every graph/value
field. Only its registered node's cache word changes inside earlier memory. -/
theorem cache_allocated_rich_normal_prefix (data : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap hashPtr node : BitVec 64)
    (output : RichOutput data frontier db source (.val (.word node)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (nonnull : node≠0#64)
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source cacheAllocated=(none,post)) :
    RichOutput data frontier db post (.val (.word node)) ∧ StablePrefix source post frontier ∧
      (∀ key,key≠ofString "heap_ptr"→post.globals.lookup key=source.globals.lookup key) := by
  obtain ⟨physical,stable,globals,⟨next,nextCell,grows⟩,memory⟩:=cache_allocated_normal_frame data source post frontier db heap hashPtr node
    output.1 heapCell nonnull hashCell nodeCell installed normal
  obtain ⟨actualHeap,child,valueEq,actualCell,registry,member⟩:=output.2
  have sameHeap : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  have sameChild : child=node:=HolWordLab.word.inj (ValueHOL.val.inj valueEq.symm)
  subst child
  have domain:=(Input.evaluation_fields source post cacheAllocated none normal).1
  have agree : ∀ query,registry.graph.Footprint query→post.memory query=source.memory query:=by
    intro query required
    have before:=(registry.graph.footprint_bounds frontier heap.toNat registry.regions query required).2
    apply memory query before
    obtain ⟨other,offset,otherMember,active,inside,notCache,equal⟩:=required.location registry.graph query
    rw [equal]
    exact registry.graph.cache_away frontier heap.toNat registry.regions registry.disjoint node other offset member nonnull otherMember active inside notCache
  have valueAgree : ∀ query,TrieWalk.ValueFootprint registry.graph query→post.memory query=source.memory query:=by
    intro query required
    have before:=(registry.graph.value_bounds frontier heap.toNat registry.regions query required).2
    apply memory query before
    obtain ⟨other,offset,otherMember,active,inside,notCache,equal⟩:=required.location registry.graph query
    rw [equal]
    exact registry.graph.cache_away frontier heap.toNat registry.regions registry.disjoint node other offset member nonnull otherMember active inside notCache
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source post 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint domain agree valueAgree
  let nextRegistry : NodeRegistry post frontier next db:=⟨graph,values,regions.weaken graph frontier heap.toNat frontier next.toNat (Nat.le_refl _) grows,disjoint⟩
  have nextMember : nextRegistry.graph.valid node:=by change graph.valid node; rw [validEq]; exact member
  exact ⟨⟨physical,next,node,rfl,nextCell,nextRegistry,nextMember⟩,stable,globals⟩

theorem suffix_rich_normal_prefix (data : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db hashPtr node : BitVec 64) (returned : ValueHOL 64)
    (output : RichOutput data frontier db source (.val (.word node)))
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterMaterialize=(some (.returned returned),post)) :
    returned=.val (.word node) ∧ RichOutput data frontier db post returned ∧ WitnessCore.Stack.StablePrefix source post frontier ∧
      (∀ key,key≠ofString "heap_ptr"→post.globals.lookup key=source.globals.lookup key) := by
  rw [suffix_shape] at normal
  obtain ⟨middle,guardRun,footerRun,nodeFrame⟩:=cache_prefix.normal_continue source post (.return (localVar "nd")) returned normal
  have guarded : RichOutput data frontier db middle (.val (.word node)) ∧ WitnessCore.Stack.StablePrefix source middle frontier ∧
      (∀ key,key≠ofString "heap_ptr"→middle.globals.lookup key=source.globals.lookup key) := by
    rw [cache_choice source node nodeCell] at guardRun
    by_cases zero : node=0#64
    · rw [if_pos zero] at guardRun
      have same : source=middle:=congrArg Prod.snd guardRun
      rw [←same]; exact ⟨output,fun _ _=>rfl,fun _ _=>rfl⟩
    · rw [if_neg zero] at guardRun
      have savedOutput:=output.1
      obtain ⟨heap,child,valueEq,heapCell,rest⟩:=savedOutput
      exact cache_allocated_rich_normal_prefix data source middle frontier db heap hashPtr node output heapCell zero hashCell nodeCell installed guardRun
  have middleNode : middle.locals.lookup (ofString "nd")=some (.val (.word node)):=nodeFrame.trans nodeCell
  obtain ⟨read,postEq⟩:=Input.return_normal middle post (localVar "nd") returned footerRun
  have actualRead : eval middle (localVar "nd")=some (.val (.word node)):=by simp [eval,localVar,evalHOLExact,toExact,middleNode]
  have returnedEq : returned=.val (.word node):=Option.some.inj (read.symm.trans actualRead)
  refine ⟨returnedEq,?_,?_,?_⟩
  · rw [returnedEq]
    apply guarded.1.of_erase data frontier db middle post (.val (.word node))
    rw [postEq]; rfl
  · intro query upper
    rw [postEq]
    exact guarded.2.1 query upper
  · intro key notHeap
    rw [postEq]
    exact guarded.2.2 key notHeap

theorem after_lookup_rich_normal_prefix_scratch (data : Input.CurrentTable.NodeBuild.Data)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root cursor limit : BitVec 64) (answer : ValueHOL 64)
    (database : Input.CurrentTable.NodeLookup.Database source data) (result : Input.CurrentTable.NodeLookup.Result data answer)
    (tableBefore : (Input.CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (rCell : source.locals.lookup (ofString "r")=some answer)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (scratch : Rlp.Validation.Arena source cursor limit)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLookup=(some (.returned returned),post)) :
    RichOutput data heap.toNat data.table post returned ∧ StablePrefix source post heap.toNat ∧
      post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)) := by
  have safe : Input.LocalPrefix (ofString "db") missingGuard:=.ite _ (.call none _ _ (by simp)) .skip
  rw [lookup_tail_shape.1] at normal
  obtain ⟨middle,guardRun,continued,dbFrame⟩:=safe.normal_continue source post materializeCall returned normal
  obtain ⟨passed,same⟩:=Fail.guard_normal source middle missingTest [.const 1#64] live.code guardRun
  subst middle
  rcases database.result result with absent|⟨pointer,length,present,allocated,small,lower,before⟩
  · rw [absent] at rCell
    have rejected : eval source missingTest=some (.val (.word 1#64)):=by
      simp [eval,missingTest,localVar,evalHOLExact,toExact,rCell,Input.CurrentTable.NodeLookup.absentValue,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using rejected.symm.trans passed
    exact ((by decide : (1#64 : BitVec 64)≠0#64) impossible).elim
  · rw [present] at rCell
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) materializeArguments=
        some (WitnessMaterialize.values data.table pointer length):=by
      simp [materializeArguments,WitnessMaterialize.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,rCell,
        Input.CurrentTable.NodeLookup.presentValue]
    obtain ⟨callee,called,entryDb,entryPointer,entryLength⟩:=WitnessMaterialize.environment source.code.lookup data.table pointer length
      (WitnessMaterialize.original_code source.code live.code)
    rw [lookup_tail_shape.2] at continued
    obtain ⟨funded,target,childReturn,inner,childRun,checked,suffixRun,endpoint⟩:=Input.CallNormal.scoped_normal source post "nd" .one
      (ofString "_decode_witness_node") materializeArguments _ WitnessMaterialize.body afterMaterialize callee .one args called returned continued
    let entry:=callEntryStateHOLFinite source callee
    have entryDatabase:=database.of_frame (show Input.LocalEffects.erase entry=Input.LocalEffects.erase source from rfl)
    have entryArena:=scratch.of_fields source entry cursor limit rfl rfl
    have childResult:=WitnessMaterialize.rich_body_normal_prefix data entry target data.table pointer length heap cursor limit
      entryDatabase tableBefore rfl entryDb entryPointer entryLength heapCell heapArena heapBound aligned heapArena.lower
      (live.of_frame rfl) entryArena before small lower live.code childReturn childRun
    have physical:=childResult.1.1
    obtain ⟨nextHeap,node,childEq,childHeap,rest⟩:=physical
    let ready:=Input.CallNormal.continuationEntry source target "nd" childReturn
    have readyOutput : RichOutput data heap.toNat data.table ready (.val (.word node)):=by
      rw [←childEq]
      exact childResult.1.of_erase data heap.toNat data.table target ready childReturn rfl
    have readyRoot : ready.locals.lookup (ofString "root_hash")=some (.val (.word root)):=
      (Input.CallNormal.continuation_lookup_other source target "nd" "root_hash" childReturn (by decide)).trans rootCell
    have readyNode : ready.locals.lookup (ofString "nd")=some (.val (.word node)):=
      (Input.CallNormal.continuation_lookup_same source target "nd" childReturn).trans (congrArg some childEq)
    have codeEq:=(Input.evaluation_fields entry target WitnessMaterialize.body (some (.returned childReturn)) childRun).2.2.2
    have readyInstalled : Input.OriginalCode.Installed ready.code:=by change Input.OriginalCode.Installed target.code; rw [codeEq]; exact live.code
    have completed:=suffix_rich_normal_prefix data ready inner heap.toNat data.table root node returned readyOutput readyRoot readyNode readyInstalled suffixRun
    refine ⟨completed.2.1.of_erase data heap.toNat data.table inner post returned (by rw [endpoint]; rfl),?_,?_⟩
    · intro query earlier
      have endMemory : post.memory=inner.memory:=by rw [endpoint]; rfl
      exact (congrFun endMemory query).trans ((completed.2.2.1 query earlier).trans (childResult.2.2 query earlier))
    · rw [endpoint]
      exact (completed.2.2.2 (ofString "scratch_ptr") (by decide)).trans childResult.2.1

/-- The literal empty-root result owns no node and retains the actual
built database and bounded heap. -/
theorem empty_rich_output (data : Input.CurrentTable.NodeBuild.Data)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor : BitVec 64)
    (database : Input.CurrentTable.NodeLookup.Database source data)
    (tableBefore : (Input.CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (scratchCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))) :
    RichOutput data heap.toNat data.table source (.val (.word 0#64)) := by
  have physical:=empty_output data source heap cursor database tableBefore heapCell heapArena heapBound aligned scratchCell
  let registry:=NodeRegistry.empty source heap.toNat heap data.table
  exact ⟨physical,heap,0#64,rfl,heapCell,registry,registry.graph.null⟩

/-- The complete actual current root decoder retains its bounded heap,
node database, earlier caller memory and incoming scratch cursor. Missing
or nonscalar empty-root operands cannot yield the observed normal return. -/
theorem current_rich_body_normal_prefix_scratch (data : Input.CurrentTable.NodeBuild.Data)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root cursor limit : BitVec 64)
    (database : Input.CurrentTable.NodeLookup.Database source data)
    (tableBefore : (Input.CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (scratch : Rlp.Validation.Arena source cursor limit)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    RichOutput data heap.toNat data.table post returned ∧ StablePrefix source post heap.toNat ∧
      post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)) := by
  rcases current_lookup_normal_trace_any source post data.table root live.code dbCell rootCell returned normal with empty|lookup
  · obtain ⟨returnedEq,pure⟩:=empty
    rw [returnedEq]
    refine ⟨(empty_rich_output data source heap cursor database tableBefore heapCell heapArena heapBound aligned scratch.cursorGlobal).of_erase
      data heap.toNat data.table source post (.val (.word 0#64)) pure,?_,?_⟩
    · intro query earlier
      exact congrFun (Input.LocalEffects.memory_of_erase source post pure) query
    · have globals:=congrArg PanSemStateFiniteExact.globals pure
      change post.globals=source.globals at globals
      rw [globals]; exact scratch.cursorGlobal
  · obtain ⟨lookupSource,lookupPost,lookupPure,lookupDb,lookupRoot,lookupRun,postPure⟩:=lookup
    have lookupDatabase:=database.of_frame lookupPure
    have lookupInstalled : Input.OriginalCode.Installed lookupSource.code:=by
      rw [Input.LocalEffects.code_of_erase source lookupSource lookupPure]; exact live.code
    obtain ⟨caller,answer,inner,callerPure,callerDb,callerRoot,callerR,result,continued,lookupEnd⟩:=
      lookup_normal data lookupSource lookupPost root lookupDatabase lookupInstalled lookupDb lookupRoot returned lookupRun
    have wholePure:=callerPure.trans lookupPure
    have callerDatabase:=database.of_frame wholePure
    have globals:=congrArg PanSemStateFiniteExact.globals wholePure
    change caller.globals=source.globals at globals
    have domain:=congrArg PanSemStateFiniteExact.memaddrs wholePure
    change caller.memaddrs=source.memaddrs at domain
    have callerHeap : caller.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
    have callerScratch:=scratch.of_fields source caller cursor limit domain globals
    have completed:=after_lookup_rich_normal_prefix_scratch data caller inner heap root cursor limit answer callerDatabase result tableBefore
      callerDb callerRoot callerR callerHeap heapArena heapBound aligned (live.of_frame wholePure) callerScratch returned continued
    have finalPure : Input.LocalEffects.erase post=Input.LocalEffects.erase inner:=postPure.trans (by rw [lookupEnd]; rfl)
    refine ⟨completed.1.of_erase data heap.toNat data.table inner post returned finalPure,?_,?_⟩
    · intro query earlier
      exact (congrFun (Input.LocalEffects.memory_of_erase inner post finalPure) query).trans
        ((completed.2.1 query earlier).trans (congrFun (Input.LocalEffects.memory_of_erase source caller wholePure) query))
    · have finalGlobals:=congrArg PanSemStateFiniteExact.globals finalPure
      change post.globals=inner.globals at finalGlobals
      rw [finalGlobals]
      exact completed.2.2

/-- Actual normal return restores the named scratch cursor and preserves
all other nonallocator globals, so its full live scratch/code/domain
contract is derived from the same observed execution. -/
theorem current_rich_body_normal_live (data : Input.CurrentTable.NodeBuild.Data)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root cursor limit : BitVec 64)
    (database : Input.CurrentTable.NodeLookup.Database source data)
    (tableBefore : (Input.CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (scratch : Rlp.Validation.Arena source cursor limit)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    RichOutput data heap.toNat data.table post returned ∧ StablePrefix source post heap.toNat ∧
      post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)) ∧ Rlp.LiveArena post ∧
      (∀ key,key≠ofString "heap_ptr"→key≠ofString "scratch_ptr"→post.globals.lookup key=source.globals.lookup key) := by
  obtain ⟨output,memory,actualScratch⟩:=current_rich_body_normal_prefix_scratch data source post heap root cursor limit
    database tableBefore dbCell rootCell heapCell heapArena heapBound aligned live scratch returned normal
  have fields:=Input.evaluation_fields source post body (some (.returned returned)) normal
  have other (key : MlS) (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") :
      post.globals.lookup key=source.globals.lookup key:=by
    have retained:=globals key source.code live.code notHeap notScratch source rfl
    rw [normal] at retained
    exact congrArg Prod.snd retained
  have restored:=live.of_cursors fields.1 fields.2.2.2 (actualScratch.trans scratch.cursorGlobal.symm)
    (other (ofString "frame_mem_ptr") (by decide) (by decide))
  exact ⟨output,memory,actualScratch,restored,other⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.cache_allocated_rich_normal_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.suffix_rich_normal_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.after_lookup_rich_normal_prefix_scratch
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.empty_rich_output
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.current_rich_body_normal_prefix_scratch
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.current_rich_body_normal_live
