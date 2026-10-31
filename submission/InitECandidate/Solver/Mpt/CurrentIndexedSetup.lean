import InitECandidate.Solver.Mpt.CurrentIndexedLoop
import InitECandidate.Solver.Mpt.IndexedPrefixCost
import InitECandidate.Solver.Mpt.CurrentTrieRoot
import InitECandidate.Solver.Input.HeapScopeCost

namespace InitECandidate.Solver.Mpt.CurrentIndexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString QueryBranch Input

def rootArguments : List (ExpHOL 64):=[localVar "m",localVar "out"]
def rootCall : ProgHOL 64:=.call (some (none,none)) (ofString "mpt_root") rootArguments
def releaseArguments : List (ExpHOL 64):=[localVar "mark"]
def releaseCall : ProgHOL 64:=.call (some (none,none)) (ofString "heap_release") releaseArguments

set_option maxRecDepth 100000 in
theorem after_loop_shape : Indexed.afterLoop=.seq rootCall (.seq releaseCall (.return (.const 0#64))) := by
  simp only [Indexed.afterLoop,Indexed.loopAndAfter,Indexed.afterNew,Indexed.afterMark,Indexed.body,Guest.guestFn_build_mpt_indexed,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,rootCall,rootArguments,releaseCall,releaseArguments,localVar]

/-- The observed ignored root call can return normally only for a zero
root. Its physical frame follows from that same callee execution. -/
theorem root_call_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {m array out empty : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices) (roots : RootInputs source out empty)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (normal : evaluateHOLFiniteState source rootCall=(none,target)) :
    model.root=0#64 ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧ target.locals=source.locals ∧
      ∀ query : BitVec 64,CopyGeneral.Away out query 32→target.memory query=source.memory query := by
  obtain ⟨callee,called,mLocal,outLocal⟩:=word_pair_environment source.code.lookup (ofString "mpt_root") (ofString "m") (ofString "out")
    CurrentTrieRoot.Root.body .one m out (by decide) (CurrentTrieRoot.Root.original_code source.code model.installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rootArguments=some [.val (.word m),.val (.word out)]:=by
    simp [rootArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.mCell,outCell]
  have mapped : source.memaddrs m:=by
    simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source m 16 0 model.domain model.headerArena (by decide) model.headerAligned (by decide)
  let entry : CurrentTrieRoot.Root.Entry (callEntryStateHOLFinite source callee) m out empty model.root cutoff model.heap.toNat:={
    arena:=⟨roots.arena.scratch,roots.arena.frame,roots.arena.domain,roots.arena.code⟩
    mCell:=mLocal,outCell:=outLocal,headerMapped:=mapped,rootStored:=model.rootStored
    emptyGlobal:=roots.emptyGlobal,emptyArena:=roots.emptyArena,outArena:=roots.outArena
    graph:=model.graph,member:=model.member,regions:=model.regions,uncached:=model.rootUncached }
  obtain ⟨funded,child,returned,run⟩:=CallNormal.ignored_callee_return source target (ofString "mpt_root") rootArguments _ CurrentTrieRoot.Root.body callee .one args called normal
  obtain ⟨zero,answer,frame,memory⟩:=CurrentTrieRoot.Root.body_normal entry returned run
  have endpoint:=CallNormal.ignored_target source target (ofString "mpt_root") rootArguments _ CurrentTrieRoot.Root.body callee .one args called returned child run normal
  rw [endpoint]
  exact ⟨zero,frame,rfl,memory⟩

/-- A genuine normal indexed-builder return forces the actual row count
to zero: every nonempty row installs a nonzero uncached root, whereas the
actual root helper returns normally only for the empty root. -/
theorem normal_count_zero {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {array out empty : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices) (roots : RootInputs source out empty) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Indexed.body=(some (.returned value),target)) : count=0 := by
  rcases Indexed.prefix_trace source target data.installed (some (.returned value)) normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨entered,inner,execution,forward,price,endpoint,remaining⟩:=reached
    obtain ⟨cutoff,⟨model⟩,clock,older,globals,outEntered,markEntered⟩:=data.setup execution
    obtain ⟨arena,enteredEq⟩:=Indexed.setup_from_execution source entered data.heap data.installed data.heapCell data.domain data.heapArena data.heapAligned execution
    have initialIndex : model.index=0#64:=by
      have expected:= (Indexed.loop_entry_locals source data.heap).2
      rw [←enteredEq] at expected
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using model.indexCell.symm.trans expected
    rw [Indexed.loop_shape] at remaining
    have safe : LocalPrefix (ofString "n") (.while Indexed.test Indexed.loopBody):=.loop Indexed.test Indexed.loop_body_limit
    obtain ⟨current,loopRun,suffixRun⟩:=sequence_returned entered inner (.while Indexed.test Indexed.loopBody) Indexed.afterLoop value
      (fun returned=>(safe.summary_full entered).2.1 returned) remaining
    obtain ⟨final,finished,grows,nextGlobals,nextMemory,positive⟩:=loop_normal model loopRun
    have currentGlobals : HeapGlobals source current:=fun name other=>(nextGlobals name other).trans (globals name other)
    have currentRoots : RootInputs current out empty:={
      arena:=⟨(currentGlobals _ (by decide)).trans roots.arena.scratch,(currentGlobals _ (by decide)).trans roots.arena.frame,final.domain,final.installed⟩
      emptyGlobal:=(currentGlobals _ (by decide)).trans roots.emptyGlobal,emptyArena:=roots.emptyArena,outArena:=roots.outArena }
    have outCurrent : current.locals.lookup (ofString "out")=some (.val (.word out)):=
      (Indexed.loop_saved entered current (ofString "out") (by decide) (by decide) loopRun).trans (outEntered.trans data.outCell)
    rw [after_loop_shape] at suffixRun
    obtain ⟨copied,rootRun,footerRun⟩:=sequence_returned current inner rootCall (.seq releaseCall (.return (.const 0#64))) value
      (fun returned=>NoReturn.ignored_call (ofString "mpt_root") rootArguments current returned) suffixRun
    have zero:=(root_call_normal final currentRoots outCurrent rootRun).1
    by_contra nonzero
    have active : model.index.toNat<count:=by rw [initialIndex]; change 0<count; omega
    exact positive (Or.inr active) zero

/-- A normal whole builder returns zero, releases its actual saved heap
mark and preserves older memory outside its owned 32-byte root output.
All frames come from this execution of the unchanged current body. -/
theorem body_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {array out empty : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices) (roots : RootInputs source out empty) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Indexed.body=(some (.returned value),target)) :
    count=0 ∧ value=.val (.word 0#64) ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word data.heap)) ∧ HeapGlobals source target ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query.toNat<data.heap.toNat→CopyGeneral.Away out query 32→target.memory query=source.memory query := by
  have zero:=normal_count_zero data roots value normal
  subst count
  obtain ⟨entered,inner,execution,clock,remaining⟩:=Indexed.setup_trace source target value normal
  obtain ⟨cutoff,⟨model⟩,enteredClock,older,globals,outEntered,markEntered⟩:=data.setup execution
  have read : eval entered Indexed.test=some (.val (.word 0#64)):=by
    have expected:=Indexed.test_read entered model.index 0 model.countBound model.indexCell model.countCell
    simpa only [Nat.not_lt_zero,if_false] using expected
  have skipped : evaluateHOLFiniteState entered (.while Indexed.test Indexed.loopBody)=(none,entered):=by
    rw [evaluateHOLFiniteState_while_total]
    simp only [eval,evalHOLFinite] at read ⊢
    rw [read]
    simp
  rw [Indexed.loop_shape,evaluateHOLFiniteState_seq_line780,skipped] at remaining
  have enteredRoots : RootInputs entered out empty:={
    arena:=⟨(globals _ (by decide)).trans roots.arena.scratch,(globals _ (by decide)).trans roots.arena.frame,model.domain,model.installed⟩
    emptyGlobal:=(globals _ (by decide)).trans roots.emptyGlobal,emptyArena:=roots.emptyArena,outArena:=roots.outArena }
  rw [after_loop_shape] at remaining
  obtain ⟨copied,rootRun,footerRun⟩:=sequence_returned entered inner rootCall (.seq releaseCall (.return (.const 0#64))) value
    (fun returned=>NoReturn.ignored_call (ofString "mpt_root") rootArguments entered returned) remaining
  obtain ⟨rootZero,copyFrame,copyLocals,copyMemory⟩:=root_call_normal model enteredRoots (outEntered.trans data.outCell) rootRun
  have copyGlobals:=congrArg PanSemStateFiniteExact.globals copyFrame
  change copied.globals=entered.globals at copyGlobals
  have copiedHeap : copied.globals.lookup (ofString "heap_ptr")=some (.val (.word model.heap)):=by rw [copyGlobals]; exact model.heapCell
  have copiedMark : copied.locals.lookup (ofString "mark")=some (.val (.word data.heap)):=by rw [copyLocals]; exact markEntered
  have copiedInstalled : OriginalCode.Installed copied.code:=by
    have codeEq:=MemoryMetadata.code copyFrame
    change copied.code=entered.code at codeEq
    rw [codeEq]; exact model.installed
  obtain ⟨released,releaseRun,returnRun⟩:=sequence_returned copied inner releaseCall (.return (.const 0#64)) value
    (fun returned=>NoReturn.ignored_call (ofString "heap_release") releaseArguments copied returned) footerRun
  obtain ⟨callee,called,mLocal⟩:=CallNormal.unary_environment copied.code.lookup (ofString "heap_release") "m" HeapScope.releaseBody data.heap
    (HeapScope.release_original_code copied.code copiedInstalled)
  have args : evalListHOLFinite copied (h:=fun query=>Classical.propDecidable (copied.memaddrs query)) releaseArguments=some [.val (.word data.heap)]:=by
    simp [releaseArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,copiedMark]
  have funded:=(CallNormal.ignored_callee_return copied released (ofString "heap_release") releaseArguments _ HeapScope.releaseBody callee .one args called releaseRun).1
  have executed:=HeapScope.release_call_execute copied data.heap model.heap releaseArguments args copiedHeap
    (HeapScope.release_original_code copied.code copiedInstalled) funded
  have releasedEq : released=HeapScope.releasePost {copied with clock:=copied.clock-1} data.heap:=congrArg Prod.snd (releaseRun.symm.trans executed)
  obtain ⟨answer,innerEq⟩:=return_normal released inner (.const 0#64) value returnRun
  have valueEq : value=.val (.word 0#64):=Option.some.inj (answer.symm.trans rfl)
  have finalFrame:=execution.erase Indexed.loopAndAfter
  rw [←Indexed.body_shape,normal] at finalFrame
  have continued : evaluateHOLFiniteState entered Indexed.loopAndAfter=(some (.returned value),inner):=by
    rw [Indexed.loop_shape,evaluateHOLFiniteState_seq_line780,skipped,after_loop_shape]
    exact remaining
  rw [continued,innerEq,releasedEq] at finalFrame
  have finalGlobals:=congrArg PanSemStateFiniteExact.globals finalFrame
  change target.globals=(HeapScope.releasePost copied data.heap).globals at finalGlobals
  have finalMemory:=congrArg PanSemStateFiniteExact.memory finalFrame
  change target.memory=copied.memory at finalMemory
  have releasedMetadata : MemoryMetadata.erase (HeapScope.releasePost copied data.heap)=MemoryMetadata.erase (HeapScope.releasePost entered data.heap):=
    congrArg (fun state=>HeapScope.releasePost state data.heap) copyFrame
  have restoredMetadata : MemoryMetadata.erase (HeapScope.releasePost entered data.heap)=MemoryMetadata.erase source:=by
    obtain ⟨arena,enteredEq⟩:=Indexed.setup_from_execution source entered data.heap data.installed data.heapCell data.domain data.heapArena data.heapAligned execution
    rw [enteredEq]
    have restoredGlobals : (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded data.heap 16#64)))).update
        (ofString "heap_ptr",.val (.word data.heap))=source.globals:=by
      apply HolFiniteMapExact.ext
      funext name
      simp only [HolFiniteMapExact.lookup_update_pointwise]
      by_cases same : name=ofString "heap_ptr"
      · subst name; simpa using data.heapCell.symm
      · simp [same]
    change {MemoryMetadata.erase source with globals:=((source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded data.heap 16#64)))).update
      (ofString "heap_ptr",.val (.word data.heap)))}=MemoryMetadata.erase source
    rw [restoredGlobals]
    rfl
  have metadata : MemoryMetadata.erase target=MemoryMetadata.erase source:=
    (MemoryMetadata.of_frame finalFrame).trans (releasedMetadata.trans restoredMetadata)
  have fields:=evaluation_fields source target Indexed.body (some (.returned value)) normal
  refine ⟨rfl,valueEq,fields.1,fields.2.1,fields.2.2.2,?_,?_,metadata,?_⟩
  · rw [finalGlobals]
    simp [HeapScope.releasePost,HolFiniteMapExact.update,FUPDATE]
  · intro name other
    rw [finalGlobals]
    change (copied.globals.update (ofString "heap_ptr",.val (.word data.heap))).lookup name=source.globals.lookup name
    simpa [HolFiniteMapExact.update,FUPDATE,Ne.symm other,copyGlobals] using globals name other
  · intro query before away
    rw [finalMemory]
    exact (copyMemory query away).trans (older query before)

/-- The real root call, real heap release and final return cost at most
seven source ticks, including every stopped/short-clock outcome. -/
theorem after_loop_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array out empty : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices) (roots : RootInputs source out empty)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    source.clock-(evaluateHOLFiniteState source Indexed.afterLoop).2.clock≤7 := by
  obtain ⟨callee,called,mLocal,outLocal⟩:=word_pair_environment source.code.lookup (ofString "mpt_root") (ofString "m") (ofString "out")
    CurrentTrieRoot.Root.body .one m out (by decide) (CurrentTrieRoot.Root.original_code source.code model.installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rootArguments=some [.val (.word m),.val (.word out)]:=by
    simp [rootArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.mCell,outCell]
  have mapped : source.memaddrs m:=by
    simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source m 16 0 model.domain model.headerArena (by decide) model.headerAligned (by decide)
  let entry : CurrentTrieRoot.Root.Entry (callEntryStateHOLFinite source callee) m out empty model.root cutoff model.heap.toNat:={
    arena:=⟨roots.arena.scratch,roots.arena.frame,roots.arena.domain,roots.arena.code⟩
    mCell:=mLocal,outCell:=outLocal,headerMapped:=mapped,rootStored:=model.rootStored
    emptyGlobal:=roots.emptyGlobal,emptyArena:=roots.emptyArena,outArena:=roots.outArena
    graph:=model.graph,member:=model.member,regions:=model.regions,uncached:=model.rootUncached }
  have price:=ClockCost.call_current source (some none) (ofString "mpt_root") rootArguments _ CurrentTrieRoot.Root.body callee .one 5 args called
    (CurrentTrieRoot.Root.body_cost entry)
  have released : ClockCost.Bound source.code releaseCall 1:=HeapScope.release_call_cost source.code model.installed (some none) releaseArguments
  have tail : ClockCost.Bound source.code (.seq releaseCall (.return (.const 0#64))) 1:=by
    exact ClockCost.sequence source.code _ _ 1 0 released (ClockCost.returned source.code _)
  rw [after_loop_shape]
  exact ClockCost.sequence_current source rootCall _ 6 1 price tail

/-- Complete unchanged current266, from actual physical rows and startup
buffers. Prefix, repeated loop, root calculation and heap release are all
included; no helper success or final normal return is assumed. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array out empty : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices) (roots : RootInputs source out empty) :
    source.clock-(evaluateHOLFiniteState source Indexed.body).2.clock≤36827*count+11 := by
  let output:=evaluateHOLFiniteState source Indexed.body
  rcases to_after_loop data output.1 rfl with stopped|reached
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨current,inner,cutoff,⟨model,finished⟩,forward,price,endpoint,remaining,globals,older,outCell,markCell⟩:=reached
    have currentRoots : RootInputs current out empty:={
      arena:=⟨(globals _ (by decide)).trans roots.arena.scratch,(globals _ (by decide)).trans roots.arena.frame,model.domain,model.installed⟩
      emptyGlobal:=(globals _ (by decide)).trans roots.emptyGlobal,emptyArena:=roots.emptyArena,outArena:=roots.outArena }
    have suffix:=after_loop_cost model currentRoots outCell
    have nextClock:=evaluateHOLFiniteState_clock_le current Indexed.afterLoop
    rw [remaining] at suffix nextClock
    change current.clock-inner.clock≤7 at suffix
    change inner.clock≤current.clock at nextClock
    change source.clock-output.2.clock≤36827*count+11
    have clocks : output.2.clock=inner.clock:=endpoint
    rw [clocks]
    omega

theorem uniform_body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array out empty : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices) (roots : RootInputs source out empty) (bounded : count≤12582752) :
    source.clock-(evaluateHOLFiniteState source Indexed.body).2.clock≤463385007915 := by
  have price:=body_cost data roots
  omega

end InitECandidate.Solver.Mpt.CurrentIndexed

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.root_call_normal
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.normal_count_zero
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.body_normal
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.after_loop_cost
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.body_cost
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.uniform_body_cost
