import InitECandidate.Solver.Mpt.WitnessCoreStackBranchTransport
import InitECandidate.Solver.Mpt.WitnessCoreStackExtension
import InitECandidate.Solver.Mpt.WitnessCoreStackCache
import InitECandidate.Solver.Mpt.WitnessCoreReturnDispatch

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def StableLocal (name : String) : Prop:=name="db" ∨ name="go" ∨ name="cur_p" ∨ name="cur_n"

/-- Complete physical outcome of an active return iteration. The actual
heap/scratch and branch-or-pop state are retained together with the
protected older-storage band and the four unchanged loop inputs. -/
def ReturnStep (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit child slot : BitVec 64) (entry : Entry) (rest : List Entry) : Prop:=
  ∃ next,
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
    AllocatedBytes.Arena next 0 ∧ next.toNat%8=0 ∧ heap.toNat≤next.toNat ∧
    Rlp.Validation.Arena post cursor limit ∧ BranchStep post db next cursor limit child slot entry rest ∧
    (∀ key,key≠ofString "heap_ptr"→ post.globals.lookup key=source.globals.lookup key) ∧
    post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code ∧
    (∀ query : BitVec 64,entry.record.toNat+88≤query.toNat→ query.toNat<entry.data.payload.startAddress→ post.memory query=source.memory query) ∧
    (∀ name : String,StableLocal name→ post.locals.lookup (ofString name)=source.locals.lookup (ofString name))

theorem cache_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child hash : BitVec 64)
    (lower upper : Nat) (owned : ResultOwned source lower upper child) (query : BitVec 64) (before : query.toNat<lower) :
    (returnCacheState source child hash).memory query=source.memory query := by
  rcases owned with zero|allocated
  · rw [returnCacheState,if_pos (Or.inr zero)]
  · have upperBound:=allocated.arena.upper
    have fresh:=allocated.fresh
    have number : (child+24#64).toNat=child.toNat+24:=byteAddress_toNat child 24 (by omega)
    exact return_cache_memory source child hash query (by intro same; have numeric:=congrArg BitVec.toNat same; rw [number] at numeric; omega)

/-- The actual stage dispatch, before closing the pending-HASH scope,
derives the physical advancing/popped state from the real continuation.
It assumes no future successful call, parser or allocation. -/
theorem return_stages_stack_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit child slot : BitVec 64) (entry : Entry) (rest : List Entry)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (owned : ResultOwned source entry.mark heap.toNat child)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word slot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word 0#64)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source returnStages=(none,post)) : ReturnStep source post db heap cursor limit child slot entry rest := by
  have head:=view.records entry List.mem_cons_self
  rw [return_stages_choice source entry.record db entry.data head topCell] at normal
  cases payload : entry.data.payload with
  | extension nibbles length=>
    rw [payload] at normal
    obtain ⟨next,nextCell,nextArena,aligned,grows,scratch,tail,resultOwned,actualTop,actualResult,globals,other,memory,domain,endian,code,rank⟩:=
      return_extension_stack_normal source post db heap cursor limit nibbles length child entry rest view payload owned topCell resultCell heapCell heapArena heapAligned arena installed normal
    have actualMode : post.locals.lookup (ofString "mode")=some (.val (.word 0#64)):=
      (other "mode" (by decide) (by decide) (by decide) (by decide)).trans modeCell
    have actualSlot : post.locals.lookup (ofString "slot")=some (.val (.word slot)):=
      (other "slot" (by decide) (by decide) (by decide) (by decide)).trans slotCell
    have step : BranchStep post db next cursor limit child slot entry rest:=
      Or.inr ⟨tail,heap,resultOwned,actualTop,actualResult,actualMode,actualSlot,rank⟩
    refine ⟨next,nextCell,nextArena,aligned,grows,scratch,step,globals,domain,endian,code,?_,?_⟩
    · intro query first last
      have above:=view.above entry List.mem_cons_self
      have before:=(view.before entry List.mem_cons_self).2
      have mark:=view.marks entry List.mem_cons_self
      change query.toNat<entry.data.payload.startAddress at last
      have startEnd : entry.data.payload.startAddress≤entry.data.payload.endAddress:=by
        simp only [payload,WitnessRecord.Payload.startAddress,WitnessRecord.Payload.endAddress]; omega
      exact memory query (by omega) (by omega)
    · intro name stable
      rcases stable with rfl|rfl|rfl|rfl <;> exact other _ (by decide) (by decide) (by decide) (by decide)
  | branch node index occupied=>
    rw [payload] at normal
    obtain ⟨step,globals,scratch,other,domain,endian,code,memory⟩:=return_branch_stack_normal source post db heap cursor limit node child slot entry rest index occupied
      view payload topCell resultCell slotCell modeCell arena installed normal
    refine ⟨heap,by rw [globals]; exact heapCell,heapArena,heapAligned,Nat.le_refl _,scratch,step,
      fun key _=>by rw [globals],domain,endian,code,memory,?_⟩
    intro name stable
    rcases stable with rfl|rfl|rfl|rfl <;> exact other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Whole unchanged active return mode: read the genuine pending HASH,
execute the conditional result cache, dispatch on the physical stage,
and close the real hash scope. Its actual branch/pop transition strictly
decreases rank while retaining the older memory/database band. -/
theorem core_return_stack_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit child slot hash : BitVec 64) (entry : Entry) (rest : List Entry)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (owned : ResultOwned source entry.mark heap.toNat child)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word slot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word 0#64)))
    (hashCell : source.memory (entry.record+80#64)=.word hash)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source returnBranch=(none,post)) : ReturnStep source post db heap cursor limit child slot entry rest := by
  have head:=view.records entry List.mem_cons_self
  rw [return_choice source entry.record topCell,if_neg (head.nonzero source entry.record db entry.data)] at normal
  obtain ⟨inner,continued,postEq⟩:=active_return_trace source post entry.record db hash entry.data head topCell hashCell none normal
  let current:=QueryBranch.bind source "hash" hash
  let cached:=returnCacheState current child hash
  have currentView:=view.of_fields source current db cursor.toNat heap.toNat (entry::rest) rfl rfl
  have currentOwned:=owned.of_fields source current child entry.mark heap.toNat rfl
  have cachedView:=cache current db child hash cursor.toNat heap.toNat entry rest currentView currentOwned
  have cachedOwned:=currentOwned.cache current child hash entry.mark heap.toNat
  have cachedGlobals : cached.globals=source.globals:=by unfold cached returnCacheState; split <;> rfl
  have cachedDomain : cached.memaddrs=source.memaddrs:=by unfold cached returnCacheState; split <;> rfl
  have cachedEndian : cached.be=source.be:=by unfold cached returnCacheState; split <;> rfl
  have cachedCode : cached.code=source.code:=by unfold cached returnCacheState; split <;> rfl
  have cachedOther (name : String) (notHash : ofString "hash"≠ofString name) :
      cached.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    unfold cached returnCacheState
    split <;> exact bind_lookup_other source "hash" name hash notHash
  have cachedResult : cached.locals.lookup (ofString "result")=some (.val (.word child)):=
    (cachedOther "result" (by decide)).trans resultCell
  have currentResult : current.locals.lookup (ofString "result")=some (.val (.word child)):=
    (bind_lookup_other source "hash" "result" hash (by decide)).trans resultCell
  rw [after_return_hash_trace current child hash head.rows.domain (currentOwned.cache_geometry current child entry.mark heap.toNat) (bind_lookup_same _ _ _) currentResult] at continued
  have cachedArena:=arena.of_fields source cached cursor limit cachedDomain cachedGlobals
  have cachedInstalled : Input.OriginalCode.Installed cached.code:=by rw [cachedCode]; exact installed
  obtain ⟨next,nextCell,nextArena,aligned,grows,scratch,step,globals,domain,endian,code,band,locals⟩:=return_stages_stack_normal cached inner db heap cursor limit child slot entry rest cachedView cachedOwned
    ((cachedOther "top" (by decide)).trans topCell) cachedResult ((cachedOther "slot" (by decide)).trans slotCell)
    ((cachedOther "mode" (by decide)).trans modeCell) (by rw [cachedGlobals]; exact heapCell)
    heapArena heapAligned cachedArena cachedInstalled continued
  have postMemory : post.memory=inner.memory:=by rw [postEq]; rfl
  have postDomain : post.memaddrs=inner.memaddrs:=by rw [postEq]; rfl
  have postGlobals : post.globals=inner.globals:=by rw [postEq]; rfl
  have postOther (name : String) (notHash : ofString "hash"≠ofString name) :
      post.locals.lookup (ofString name)=inner.locals.lookup (ofString name):=by
    rw [postEq,Input.ScalarScope.restore_other _ _ "hash" name notHash]
  have postStep:=step.of_fields inner post db next cursor limit child slot entry rest postMemory postDomain
    (postOther "top" (by decide)) (postOther "slot" (by decide)) (postOther "mode" (by decide)) (postOther "result" (by decide))
  have scratchPost:=scratch.of_fields inner post cursor limit postDomain postGlobals
  refine ⟨next,by rw [postGlobals]; exact nextCell,nextArena,aligned,grows,scratchPost,postStep,
    fun key notHeap=>(by rw [postGlobals]; exact (globals key notHeap).trans (congrArg (fun map=>map.lookup key) cachedGlobals)),
    postDomain.trans (domain.trans cachedDomain),?_,?_,?_,?_⟩
  · rw [postEq]; exact endian.trans cachedEndian
  · rw [postEq]; exact code.trans cachedCode
  · intro query first last
    rw [postMemory,band query first last]
    have before:=(view.before entry List.mem_cons_self).2
    have startEnd : entry.data.payload.startAddress≤entry.data.payload.endAddress:=by
      cases payload : entry.data.payload <;> simp only [payload,WitnessRecord.Payload.startAddress,WitnessRecord.Payload.endAddress] <;> omega
    exact cache_before current child hash entry.mark heap.toNat currentOwned query (by omega)
  · intro name stable
    have notHash : ofString "hash"≠ofString name:=by rcases stable with rfl|rfl|rfl|rfl <;> decide
    exact (postOther name notHash).trans ((locals name stable).trans (cachedOther name notHash))

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.cache_before
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.return_stages_stack_normal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.core_return_stack_normal
