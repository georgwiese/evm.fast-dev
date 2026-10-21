import InitECandidate.Solver.Mpt.WitnessCoreRegistryReturnStages

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole genuine active return mode: actual HASH read, conditional
cache, physical stage dispatch, completed-node registration or branch
advance, and the final real HASH scope restoration. -/
theorem ActiveRegistry.return_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap finalHeap cursor limit child slot hash : BitVec 64) (entry : Entry) (rest : List Entry)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,.returning,true⟩)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (owned : ResultOwned source entry.mark heap.toNat child)
    (frontierLower : 2713731432≤frontier) (frontierBefore : frontier≤heap.toNat)
    (fresh : frontier≤entry.data.payload.startAddress) (dbUpper : db.toNat≤33806089496)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word slot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word 0#64)))
    (hashCell : source.memory (entry.record+80#64)=.word hash)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (actualHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
    (normal : evaluateHOLFiniteState source returnBranch=(none,post)) :
    BranchRegistryResult post frontier db finalHeap cursor entry rest := by
  have head:=view.records entry List.mem_cons_self
  rw [return_choice source entry.record topCell,if_neg (head.nonzero source entry.record db entry.data)] at normal
  obtain ⟨inner,continued,postEq⟩:=active_return_trace source post entry.record db hash entry.data head topCell hashCell none normal
  let current:=QueryBranch.bind source "hash" hash
  let cached:=returnCacheState current child hash
  have currentView:=view.of_fields source current db cursor.toNat heap.toNat (entry::rest) rfl rfl
  have currentOwned:=owned.of_fields source current child entry.mark heap.toNat rfl
  have cachedView:=cache current db child hash cursor.toNat heap.toNat entry rest currentView currentOwned
  have cachedOwned:=currentOwned.cache current child hash entry.mark heap.toNat
  obtain ⟨currentRegistry,currentValid⟩:=registry.of_fields source current frontier db _ rfl rfl (bind_lookup_other source "hash" "result" hash (by decide))
  have currentResult : current.locals.lookup (ofString "result")=some (.val (.word child)) :=
    (bind_lookup_other source "hash" "result" hash (by decide)).trans resultCell
  obtain ⟨cachedRegistry,cachedValid⟩:=currentRegistry.after_cache current frontier db heap cursor child hash entry rest currentView currentOwned
    (currentRegistry.returned rfl child currentResult)
  have cachedGlobals : cached.globals=source.globals := by unfold cached returnCacheState; split <;> rfl
  have cachedDomain : cached.memaddrs=source.memaddrs := by unfold cached returnCacheState; split <;> rfl
  have cachedCode : cached.code=source.code := by unfold cached returnCacheState; split <;> rfl
  have cachedOther (name : String) (notHash : ofString "hash"≠ofString name) :
      cached.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    unfold cached returnCacheState
    split <;> exact bind_lookup_other source "hash" name hash notHash
  rw [after_return_hash_trace current child hash head.rows.domain (currentOwned.cache_geometry current child entry.mark heap.toNat) (bind_lookup_same _ _ _) currentResult] at continued
  have cachedArena:=arena.of_fields source cached cursor limit cachedDomain cachedGlobals
  have cachedInstalled : Input.OriginalCode.Installed cached.code := by rw [cachedCode]; exact installed
  have postMemory : post.memory=inner.memory := by rw [postEq]; rfl
  have postDomain : post.memaddrs=inner.memaddrs := by rw [postEq]; rfl
  have postOther (name : String) (notHash : ofString "hash"≠ofString name) :
      post.locals.lookup (ofString name)=inner.locals.lookup (ofString name) := by
    rw [postEq,Input.ScalarScope.restore_other _ _ "hash" name notHash]
  have innerHeap : inner.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) := by rw [postEq] at actualHeap; exact actualHeap
  have stage:=cachedRegistry.return_stages_normal cached inner frontier db heap finalHeap cursor limit child slot entry rest cachedView cachedOwned
    frontierLower frontierBefore fresh dbUpper ((cachedOther "top" (by decide)).trans topCell) ((cachedOther "result" (by decide)).trans resultCell)
    ((cachedOther "slot" (by decide)).trans slotCell) ((cachedOther "mode" (by decide)).trans modeCell) (by rw [cachedGlobals]; exact heapCell)
    heapArena heapAligned cachedArena cachedInstalled innerHeap continued
  rcases stage with ⟨nextEntry,sameRecord,headView,mode,⟨innerRegistry⟩⟩|⟨mode,⟨innerRegistry⟩⟩
  · obtain ⟨postRegistry,postValid⟩:=innerRegistry.of_fields inner post frontier db _ postMemory postDomain (postOther "result" (by decide))
    exact Or.inl ⟨nextEntry,sameRecord,headView.of_fields inner post nextEntry.record db nextEntry.data postMemory postDomain,
      (postOther "mode" (by decide)).trans mode,⟨postRegistry⟩⟩
  · obtain ⟨postRegistry,postValid⟩:=innerRegistry.of_fields inner post frontier db _ postMemory postDomain (postOther "result" (by decide))
    exact Or.inr ⟨(postOther "mode" (by decide)).trans mode,⟨postRegistry⟩⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.return_normal
