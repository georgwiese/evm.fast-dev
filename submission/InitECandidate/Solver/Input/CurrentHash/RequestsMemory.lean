import InitECandidate.Solver.Input.CurrentHash.RequestsMemoryPipeline
import InitECandidate.Solver.Input.CurrentHash.RequestsCost

namespace InitECandidate.Solver.Input.CurrentHash.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_mark_memory {input : Guest.InputBlob} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq cursor chunk out zeros query : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64)
    (data : Before input source blob rq cursor chunk out zeros start size counts)
    (below : query.toNat<cursor.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.panop .mul [.const 5#64,.const 32#64]]=some (PersistentAlloc.values 160#64) := rfl
  obtain ⟨room,funded,inner,remaining,endpoint⟩ := PersistentAlloc.call_normal source post "ch" [.panop .mul [.const 5#64,.const 32#64]] afterAllocation cursor 160#64 args
    (PersistentAlloc.original_code source.code data.context.installed) (Trap.original_code source.code data.context.installed) data.context.heap data.context.heapBound value actual
  let allocated := PersistentAlloc.post {source with clock:=source.clock-1} cursor 160#64
  let entry := CallNormal.continuationEntry source allocated "ch" (.val (.word cursor))
  have ready : State input entry blob rq cursor (PersistentAlloc.rounded cursor 160#64) chunk out zeros start size counts :=
    data.allocated (target:=allocated) room rfl
  have memory := pipeline_memory RequestList.kinds entry inner blob rq cursor (PersistentAlloc.rounded cursor 160#64) chunk out zeros query start size counts
    ready below chunkAway outAway value remaining
  rw [endpoint]
  exact memory

/-- Whole current parent requests hash preserves earlier metadata outside its
real output/length chunk and restores its entering heap on this normal return. -/
theorem body_frame {input : Guest.InputBlob} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq cursor chunk out zeros query : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64)
    (data : Before input source blob rq cursor chunk out zeros start size counts)
    (below : query.toNat<cursor.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have heap := body_heap source post cursor data.context.installed data.context.heap value actual
  rw [body_shape] at actual
  obtain ⟨funded,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark data.context.heap
    (HeapScope.mark_original_code source.code data.context.installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have context : MerkleMemory.Context entry cursor zeros rq := data.context.of_frozen rfl
  have image : Requests.DecodedImage input entry blob rq start size counts := data.decoded.of_memory (by intro index inside; exact ⟨rfl,rfl⟩)
  have ready : Before input entry blob rq cursor chunk out zeros start size counts := ⟨context,image,(kept "rq" (by decide)).trans data.request,
    (kept "out" (by decide)).trans data.output,data.recordBefore,data.chunkCell,data.chunkArena,data.chunkAligned,data.chunkBefore⟩
  have memory := after_mark_memory entry inner blob rq cursor chunk out zeros query start size counts ready below chunkAway outAway value remaining
  refine ⟨?_,heap⟩
  rw [endpoint]
  exact memory

theorem call_frame {input : Guest.InputBlob} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq cursor chunk out zeros query : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64)
    (context : MerkleMemory.Context source cursor zeros rq) (decoded : Requests.DecodedImage input source blob rq start size counts)
    (recordBefore : rq.toNat+80≤cursor.toNat)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkBefore : chunk.toNat+32≤rq.toNat)
    (below : query.toNat<cursor.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values rq out))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .htr_requests) arguments)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,request,output⟩ := word_pair_environment source.code.lookup (Code.name .htr_requests) (ofString "rq") (ofString "out") body .one rq out
    (by decide) (original_code source.code context.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (Code.name .htr_requests) arguments actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  let entry := callEntryStateHOLFinite source callee
  have image : Requests.DecodedImage input entry blob rq start size counts := decoded.of_memory (by intro index inside; exact ⟨rfl,rfl⟩)
  have ready : Before input entry blob rq cursor chunk out zeros start size counts := ⟨context.at_callee callee,image,request,output,recordBefore,chunkCell,chunkArena,chunkAligned,chunkBefore⟩
  have frame := body_frame entry target blob rq cursor chunk out zeros query start size counts ready below chunkAway outAway returned bodyRun
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CurrentHash.RequestsHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.body_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.call_frame
