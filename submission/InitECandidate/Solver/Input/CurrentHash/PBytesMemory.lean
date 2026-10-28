import InitECandidate.Solver.Input.CurrentHash.PListMemory
import InitECandidate.Solver.Input.CurrentHash.PackBytesScopeMemory
import InitECandidate.Solver.Input.CurrentHash.PBytesCost
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentHash.PBytesMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open PBytesCost

theorem after_pack_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer cursor chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p out n)
    (pk : source.locals.lookup (ofString "pk")=some (PackBytesReturn.tuple buffer n)) (bounded : PackBytes.chunks n≤134217728)
    (bufferArena : AllocatedBytes.Arena buffer (PackBytes.padded n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterPack=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) listArguments =
      some (PListCost.values buffer (BitVec.ofNat 64 n) out (PackBytes.chunks n)) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listArguments,localVar,pk,PackBytesReturn.tuple,data.length,data.output,PListCost.values]
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (Code.name .htr_plist_chunks) listArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [source_shape.2.2.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have image := PListMemory.call_frame source middle buffer cursor (BitVec.ofNat 64 n) chunk out zeros query (PackBytes.chunks n) context bounded
    bufferArena outArena outAway chunkCell chunkArena chunkAligned chunkAway listArguments args normal
  have installed : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact context.installed
  rw [source_shape.2.2.2] at remaining
  exact (HeapScope.release_return_memory middle post [localVar "mark"] query installed value remaining).trans image.1

theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p out n)
    (small : n+64<2^64) (bounded : PackBytes.chunks n≤134217728)
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,packArguments,localVar,data.pointer,data.length,PackBytes.values]
  rw [source_shape.2.1] at actual
  obtain ⟨target,final,image,codeEq,domainEq,globals,remaining,endpoint⟩ := PackBytesScopeMemory.image source post p cursor query n small context.installed context.domain
    context.heap context.heapLower context.heapBound context.aligned inputArena context.below "pk" packArguments afterPack args value actual
  let entry := CallNormal.continuationEntry source target "pk" (PackBytesReturn.tuple cursor n)
  let nextCursor := PersistentAlloc.rounded cursor (BitVec.ofNat 64 (PackBytes.padded n))
  have kept (name : String) (different : ofString "pk"≠ofString name) := CallNormal.continuation_lookup_other source target "pk" name (PackBytesReturn.tuple cursor n) different
  have nextData : Params entry p out n := ⟨(kept "p" (by decide)).trans data.pointer,(kept "n" (by decide)).trans data.length,(kept "out" (by decide)).trans data.output⟩
  have pk : entry.locals.lookup (ofString "pk")=some (PackBytesReturn.tuple cursor n) := CallNormal.continuation_lookup_same _ _ _ _
  have nextCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact context.installed
  have next : MerkleMemory.Context entry nextCursor zeros query := ⟨nextCode,domainEq.trans context.domain,(globals .zeroHashes).trans context.zeroCell,
    context.zeroArena,image.heap,by have h:=image.grows; have l:=context.heapLower; dsimp [nextCursor]; omega,image.nextBound,image.nextAligned,
    by have h:=image.grows; have l:=context.below; dsimp [nextCursor]; omega⟩
  have bufferArena : AllocatedBytes.Arena cursor (PackBytes.padded n) := ⟨context.heapLower,by have h:=image.room; omega⟩
  have frame := after_pack_memory entry final p cursor nextCursor chunk out zeros query n next nextData pk bounded bufferArena outArena outAway
    ((globals .lengthChunk).trans chunkCell) chunkArena chunkAligned chunkAway value remaining
  rw [endpoint]
  exact frame.trans image.protectedWord

/-- Complete actual progressive byte hashing preserves earlier metadata and
restores its entering heap using its real packed tuple and byte length. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p out n)
    (small : n+64<2^64) (bounded : PackBytes.chunks n≤134217728)
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have heap := MarkedHeap.pbytes source post cursor context.installed context.heap value actual
  rw [source_shape.1] at actual
  obtain ⟨positive,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark context.heap
    (HeapScope.mark_original_code source.code context.installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have ready : MerkleMemory.Context entry cursor zeros query := ⟨context.installed,context.domain,context.zeroCell,context.zeroArena,context.heap,
    context.heapLower,context.heapBound,context.aligned,context.below⟩
  have next : Params entry p out n := ⟨(kept "p" (by decide)).trans data.pointer,(kept "n" (by decide)).trans data.length,(kept "out" (by decide)).trans data.output⟩
  have image := after_mark_memory entry inner p cursor chunk out zeros query n ready next small bounded inputArena outArena outAway
    chunkCell chunkArena chunkAligned chunkAway value remaining
  refine ⟨?_,heap⟩
  rw [endpoint]
  exact image

theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor chunk out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (small : n+64<2^64) (bounded : PackBytes.chunks n≤134217728)
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (CallNormal.tripleValues p (BitVec.ofNat 64 n) out))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .htr_pbytes) expressions)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have entry : source.code.lookup (Code.name .htr_pbytes)=some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],body,.one) := by
    simpa only [Code.formals,Code.body,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_pbytes,body,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using Code.installed source.code context.installed .htr_pbytes
  obtain ⟨callee,called,pointer,length,output⟩ := CallNormal.triple_environment source.code.lookup (Code.name .htr_pbytes) body p (BitVec.ofNat 64 n) out entry
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (Code.name .htr_pbytes) expressions actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have image := body_frame (callEntryStateHOLFinite source callee) target p cursor chunk out zeros query n (context.at_callee callee) ⟨pointer,length,output⟩ small bounded
    inputArena outArena outAway chunkCell chunkArena chunkAligned chunkAway returned bodyRun
  rw [endpoint]
  exact image

end InitECandidate.Solver.Input.CurrentHash.PBytesMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesMemory.after_pack_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesMemory.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesMemory.body_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesMemory.call_frame
