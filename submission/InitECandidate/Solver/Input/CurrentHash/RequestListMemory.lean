import InitECandidate.Solver.Input.CurrentHash.RequestListMemoryLoop
import InitECandidate.Solver.Input.CurrentHash.RequestListCallCost
import InitECandidate.Solver.Input.CurrentHash.PListMemory
import InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation

namespace InitECandidate.Solver.Input.CurrentHash.RequestList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots cursor chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (bounded : n≤134217728)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (rootsArena : AllocatedBytes.Arena roots (32*n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterLoop=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) listArguments=some (PListCost.values roots (BitVec.ofNat 64 n) out n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listArguments,localVar,root,count,output,PListCost.values]
  unfold afterLoop at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "htr_plist_chunks") listArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have image := PListMemory.call_frame source middle roots cursor (BitVec.ofNat 64 n) chunk out zeros query n context bounded rootsArena outArena outAway
    chunkCell chunkArena chunkAligned chunkAway listArguments args normal
  have installed : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact context.installed
  exact (HeapScope.release_return_memory middle post [localVar "mark"] query installed value remaining).trans image.1

theorem loop_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots cursor chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (bounded : n≤134217728) (data : RoundState source kind p roots out n 0)
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (rootsArena : AllocatedBytes.Arena roots (32*n)) (rootsAway : CopyGeneral.Away roots query (32*n))
    (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source loopAndSuffix=(some (.returned value),post)) : post.memory query=source.memory query := by
  unfold loopAndSuffix at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value ((loop_local (ofString "n") (by decide)).summary_full source).2.1 actual
  have image := loop_frame source middle kind p roots cursor out zeros query n 0 context data bounded (Nat.zero_le _) inputArena rootsArena rootsAway normal
  obtain ⟨position,positionBound,current⟩ := image.2.2
  have globals := loop_globals .lengthChunk source.code context.installed source rfl
  rw [normal] at globals
  have tail := after_loop_memory middle post roots cursor chunk out zeros query n image.2.1 bounded current.root current.count current.output rootsArena outArena outAway
    ((congrArg Prod.snd globals).trans chunkCell) chunkArena chunkAligned chunkAway value remaining
  exact tail.trans image.1

theorem after_roots_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots cursor chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (bounded : n≤134217728) (data : Params source kind p out n)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (rootsArena : AllocatedBytes.Arena roots (32*n)) (rootsAway : CopyGeneral.Away roots query (32*n))
    (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterRoots=(some (.returned value),post)) : post.memory query=source.memory query := by
  apply MemoryAt.declaration_returned source post "i" (.const 0#64) 0#64 query loopAndSuffix value rfl _ actual
  intro inner remaining
  let entry := bind source "i" 0#64
  have kept (name : String) (different : ofString "i"≠ofString name) := bind_lookup_other source "i" name 0#64 different
  have ready : RoundState entry kind p roots out n 0 := ⟨data.installed,(kept "kind" (by decide)).trans data.category,(kept "p" (by decide)).trans data.pointer,
    (kept "n" (by decide)).trans data.count,(kept "sz" (by decide)).trans data.size,(kept "roots" (by decide)).trans root,(kept "out" (by decide)).trans data.output,bind_lookup_same _ _ _⟩
  exact loop_suffix_memory entry inner kind p roots cursor chunk out zeros query n (context.of_frozen rfl) bounded ready inputArena rootsArena rootsAway
    outArena outAway chunkCell chunkArena chunkAligned chunkAway value remaining

/-- The same normal root-array allocation supplies its real persistent room
and next heap; only the actual record slots enter the loop/list memory frame. -/
theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source roots zeros query) (bounded : n≤134217728) (data : Params source kind p out n)
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  have amountNumber : (BitVec.ofNat 64 (32*n+32)).toNat=32*n+32 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) allocationArguments=some (PersistentAlloc.values (BitVec.ofNat 64 (32*n+32))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,allocationArguments,localVar,data.count,PersistentAlloc.values,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.mul_comm]
  unfold afterMark at actual
  apply MemoryContextAllocation.scope_memory source post roots (BitVec.ofNat 64 (32*n+32)) zeros query context "roots" allocationArguments afterRoots args _ value actual
  intro inner ready arena returned remaining
  let entry := MemoryContextAllocation.entry source roots (BitVec.ofNat 64 (32*n+32)) "roots"
  have kept (name : String) (different : ofString "roots"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other (PersistentAlloc.post {source with clock:=source.clock-1} roots (BitVec.ofNat 64 (32*n+32))) "roots" name roots different
  have nextData : Params entry kind p out n := ⟨data.installed,(kept "kind" (by decide)).trans data.category,(kept "p" (by decide)).trans data.pointer,
    (kept "n" (by decide)).trans data.count,(kept "sz" (by decide)).trans data.size,(kept "out" (by decide)).trans data.output⟩
  have slots : AllocatedBytes.Arena roots (32*n) := AllocatedBytes.Arena.weaken roots _ _ arena (by rw [amountNumber]; omega)
  have away := CopyGeneral.Away.after roots query (32*n) context.aligned (by have h:=slots.upper; omega) context.below
  have chunkEntry : entry.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded roots (BitVec.ofNat 64 (32*n+32)))))).lookup (ofString "ssz_len_chunk")=_
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "heap_ptr"≠ofString "ssz_len_chunk" from by decide] using chunkCell
  exact after_roots_memory entry inner kind p roots _ chunk out zeros query n ready bounded nextData (bind_lookup_same _ _ _) inputArena slots away
    outArena outAway chunkEntry chunkArena chunkAligned chunkAway returned remaining

/-- Complete current selected request-list hash, including its real allocation,
dispatch/loop, progressive list, release and saved scopes. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source roots zeros query) (bounded : n≤134217728) (data : Params source kind p out n)
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)) := by
  have heap := MarkedHeap.request_list source post roots context.installed context.heap value actual
  rw [body_shape] at actual
  obtain ⟨positive,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post roots "mark" afterMark context.heap
    (HeapScope.mark_original_code source.code context.installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" roots
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name roots different
  have ready : MerkleMemory.Context entry roots zeros query := ⟨context.installed,context.domain,context.zeroCell,context.zeroArena,context.heap,
    context.heapLower,context.heapBound,context.aligned,context.below⟩
  have next : Params entry kind p out n := ⟨data.installed,(kept "kind" (by decide)).trans data.category,(kept "p" (by decide)).trans data.pointer,
    (kept "n" (by decide)).trans data.count,(kept "sz" (by decide)).trans data.size,(kept "out" (by decide)).trans data.output⟩
  have image := after_mark_memory entry inner kind p roots chunk out zeros query n ready bounded next inputArena outArena outAway chunkCell chunkArena chunkAligned chunkAway value remaining
  refine ⟨?_,heap⟩
  rw [endpoint]
  exact image

theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source roots zeros query) (bounded : n≤134217728)
    (inputArena : AllocatedBytes.Arena p (n*kind.record.length)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (values kind p out n))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_request_list") expressions)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)) := by
  obtain ⟨callee,called,category,pointer,count,size,output⟩ := environment source.code context.installed kind p out n
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "htr_request_list") expressions actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have image := body_frame (callEntryStateHOLFinite source callee) target kind p roots chunk out zeros query n (context.at_callee callee) bounded
    ⟨context.installed,category,pointer,count,size,output⟩ inputArena outArena outAway chunkCell chunkArena chunkAligned chunkAway returned bodyRun
  rw [endpoint]
  exact image

end InitECandidate.Solver.Input.CurrentHash.RequestList

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.after_loop_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.loop_suffix_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.after_roots_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.body_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.call_frame
