import InitECandidate.Solver.Mpt.WitnessDecodeSuffixCost
import InitECandidate.Solver.Input.PersistentAllocationFrame
import InitECandidate.Solver.Input.Copy32SpanCall
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.WitnessRadix.RestoreLookup
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual normal root-cache allocation/copy/store protects the original
entry frontier. The returned node may precede this later cache allocation,
so its freshness is relative to that original frontier. -/
theorem current_cache_allocated_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap frontier root node : BitVec 64)
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node)))
    (beforeHeap : frontier.toNat≤heap.toNat) (fresh : frontier.toNat≤node.toNat) (nodeBound : node.toNat≤2952790016)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source)
    (normal : evaluateHOLFiniteState source cacheAllocated=(none,post)) :
    post.locals.lookup (ofString "nd")=some (.val (.word node)) ∧ PersistentNormalFrame source post frontier := by
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup 32#64 (PersistentAlloc.original_code source.code arena.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source post "h" .one (ofString "alloc") [.const 32#64]
    (PersistentAlloc.values 32#64) PersistentAlloc.body (.seq rootCopy rootCache) callee .one rfl called normal
  obtain ⟨answerEq,room,allocation⟩:=PersistentAlloc.body_persistent_frame (callEntryStateHOLFinite source callee) target heap 32#64
    amountCell heapCell heapArena heapBound arena.code answer bodyRun
  rw [answerEq] at continued
  let ready:=CallNormal.continuationEntry source target "h" (.val (.word heap))
  have allocationFrame : PersistentNormalFrame source ready heap:=allocation.of_erase _ _ source ready heap rfl rfl
  have readyArena:=allocationFrame.current_arena arena
  have currentRoot : ready.locals.lookup (ofString "root_hash")=some (.val (.word root)):=
    (CallNormal.continuation_lookup_other source target "h" "root_hash" _ (by decide)).trans rootCell
  have currentNode : ready.locals.lookup (ofString "nd")=some (.val (.word node)):=
    (CallNormal.continuation_lookup_other source target "h" "nd" _ (by decide)).trans nodeCell
  have currentH : ready.locals.lookup (ofString "h")=some (.val (.word heap)):=CallNormal.continuation_lookup_same _ _ _ _
  obtain ⟨copied,copyRun,cacheRun⟩:=sequence_none ready inner rootCopy rootCache continued
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query))
      [localVar "h",localVar "root_hash",.const 32#64]=some (CopyGeneral.values heap root 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,currentH,currentRoot,CopyGeneral.values]
  obtain ⟨copyFrame,copyLocals⟩:=Copy32Span.call_normal ready copied heap root _ args readyArena.code copyRun
  have copiedNode : copied.locals.lookup (ofString "nd")=some (.val (.word node)):=by rw [copyLocals]; exact currentNode
  have copiedH : copied.locals.lookup (ofString "h")=some (.val (.word heap)):=by rw [copyLocals]; exact currentH
  have addressRead : eval copied (addConst (localVar "nd") 24#64)=some (.val (.word (node+24#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,addConst,toExact,copiedNode,valueIsWord,valueWord,wordOpHOL,wordOp]
  have wordRead : eval copied (localVar "h")=some (.val (.word heap)):=by simp [eval,evalHOLExact,localVar,toExact,copiedH]
  obtain ⟨mapped,stored⟩:=word_store_normal copied inner _ _ (node+24#64) heap addressRead wordRead cacheRun
  have runtime : MemoryMetadata.erase post=MemoryMetadata.erase ready:=by
    rw [endpoint,stored]
    exact copyFrame.fields
  have cacheNumber : (node+24#64).toNat=node.toNat+24:=byteAddress_toNat node 24 (by omega)
  have tailMemory (query : BitVec 64) (before : query.toNat<frontier.toNat) : post.memory query=ready.memory query := by
    rw [endpoint,stored]
    have away : query≠node+24#64:=by intro same; have numeric:=congrArg BitVec.toNat same; rw [cacheNumber] at numeric; omega
    change (if query=node+24#64 then .word heap else copied.memory query)=ready.memory query
    rw [if_neg away]
    exact copyFrame.memory query (CopyGeneral.Away.after heap query 32 aligned (by omega) (by omega))
  have earlierFrame : PersistentNormalFrame source ready frontier:=
    ⟨by obtain ⟨next,cell,nextArena,nextBound,nextAligned,grows⟩:=allocationFrame.nextHeap; exact ⟨next,cell,nextArena,nextBound,nextAligned,Nat.le_trans beforeHeap grows⟩,
      allocationFrame.metadata,allocationFrame.globals,fun query before=>allocationFrame.memory query (by omega)⟩
  refine ⟨?_,earlierFrame.after_memory source ready post frontier runtime tailMemory⟩
  rw [endpoint,restore_lookup_other source inner "h" "nd" (by decide),stored]
  exact copiedNode

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.current_cache_allocated_frame
