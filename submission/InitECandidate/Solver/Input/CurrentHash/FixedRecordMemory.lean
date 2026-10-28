import InitECandidate.Solver.Input.CurrentHash.FixedRecordMemorySteps
import InitECandidate.Solver.Input.CurrentHash.FixedRecordMemoryGeometry
import InitECandidate.Solver.Input.CurrentHash.FixedRecordPipeline
import InitECandidate.Solver.Input.CurrentHash.MarkedHeap
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Input.CurrentHash.FixedRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_steps_memory (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch cursor out zeros query : BitVec 64)
    (context : MerkleMemory.Context source cursor zeros query)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (chunksArena : AllocatedBytes.Arena ch (32*kind.count)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source kind.afterSteps=(some (.returned value),post)) : post.memory query=source.memory query := by
  have number : (BitVec.ofNat 64 kind.count).toNat=kind.count := by cases kind <;> decide
  have bound : kind.count≤2^kind.depth := by cases kind <;> decide
  have small : kind.depth<58 := by cases kind <;> decide
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) kind.merkleArguments =
      some (Merkle.values ch (BitVec.ofNat 64 kind.count) (BitVec.ofNat 64 kind.count) out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,Kind.merkleArguments,localVar,chunks,output,Merkle.values]
  unfold Kind.afterSteps at actual
  have safe : LocalPrefix (ofString "ch") (.call (some (none,none)) (ofString "merkleize") kind.merkleArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have front := MerkleMemory.call_memory source middle ch (BitVec.ofNat 64 kind.count) (BitVec.ofNat 64 kind.count) out cursor zeros query kind.depth context small
    (by rw [number]; exact bound) (by rw [number]; exact bound) (by simpa only [number] using chunksArena) outArena outAway kind.merkleArguments args normal
  have installed : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact context.installed
  exact (HeapScope.release_return_memory middle post [localVar "mark"] query installed value remaining).trans front

theorem after_allocation_memory (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch cursor out zeros query : BitVec 64)
    (context : MerkleMemory.Context source cursor zeros query)
    (pointer : source.locals.lookup (ofString kind.inputName)=some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p kind.length) (chunksArena : AllocatedBytes.Arena ch (32*kind.count)) (aligned : ch.toNat%8=0) (below : query.toNat<ch.toNat)
    (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source kind.afterAllocation=(some (.returned value),post)) : post.memory query=source.memory query := by
  apply pipeline_memory kind.steps kind.inputName kind.afterSteps (steps_valid kind) source post p ch cursor zeros query context pointer chunks
    (steps_geometry kind p ch query inputArena chunksArena aligned below) _ value actual
  intro middle ready normal observed returned
  have kept (name : MlS) : middle.locals.lookup name=source.locals.lookup name := by
    have summary := (pipeline_prefix name kind.inputName kind.steps).summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  exact after_steps_memory kind middle post ch cursor out zeros query ready ((kept _).trans chunks) ((kept _).trans output) chunksArena outArena outAway observed returned

/-- A real returning allocation derives the chunk arena and next heap. The
ordinary memory extent is never substituted for persistent allocation room. -/
theorem after_mark_memory (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out zeros query : BitVec 64)
    (context : MerkleMemory.Context source ch zeros query)
    (pointer : source.locals.lookup (ofString kind.inputName)=some (.val (.word p)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p kind.length) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source kind.afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  have amountNumber : (BitVec.ofNat 64 (32*kind.count)).toNat=32*kind.count := by cases kind <;> decide
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) kind.allocationArguments=some (PersistentAlloc.values (BitVec.ofNat 64 (32*kind.count))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,Kind.allocationArguments,PersistentAlloc.values,valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,BitVec.mul_comm]
  unfold Kind.afterMark at actual
  obtain ⟨room,positive,inner,remaining,endpoint⟩ := PersistentAlloc.call_normal source post "ch" kind.allocationArguments kind.afterAllocation ch
    (BitVec.ofNat 64 (32*kind.count)) args (PersistentAlloc.original_code source.code context.installed) (Trap.original_code source.code context.installed)
    context.heap context.heapBound value actual
  have guards := PersistentAlloc.guards ch (BitVec.ofNat 64 (32*kind.count)) room
  rw [amountNumber] at room
  let allocated := PersistentAlloc.post {source with clock:=source.clock-1} ch (BitVec.ofNat 64 (32*kind.count))
  let entry := bind allocated "ch" ch
  let cursor := PersistentAlloc.rounded ch (BitVec.ofNat 64 (32*kind.count))
  have kept (name : String) (different : ofString "ch"≠ofString name) := bind_lookup_other allocated "ch" name ch different
  have currentHeap : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word cursor))).lookup (ofString "heap_ptr")=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have currentZero : entry.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word cursor))).lookup (ofString "zero_hashes")=_
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "heap_ptr"≠ofString "zero_hashes" from by decide] using context.zeroCell
  have next : MerkleMemory.Context entry cursor zeros query := ⟨context.installed,context.domain,currentZero,context.zeroArena,currentHeap,
    by have h:=guards.2.2.1; have l:=context.heapLower; dsimp [cursor]; rw [amountNumber] at h; omega,
    guards.2.2.2.1,guards.2.2.2.2,by have h:=guards.2.2.1; have l:=context.below; dsimp [cursor]; rw [amountNumber] at h; omega⟩
  have arena : AllocatedBytes.Arena ch (32*kind.count) := ⟨context.heapLower,by omega⟩
  have frame := after_allocation_memory kind entry inner p ch cursor out zeros query next ((kept kind.inputName (by cases kind <;> decide)).trans pointer)
    (bind_lookup_same _ _ _) ((kept "out" (by decide)).trans output) inputArena arena context.aligned context.below outArena outAway value remaining
  rw [endpoint]
  exact frame

/-- All six unchanged fixed-record hashes preserve earlier metadata and
restore the entering heap, using only actual input/output/workspace extents. -/
theorem body_frame (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out zeros query : BitVec 64)
    (context : MerkleMemory.Context source ch zeros query)
    (pointer : source.locals.lookup (ofString kind.inputName)=some (.val (.word p)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p kind.length) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)) := by
  have heap := MarkedHeap.fixed kind source post ch context.installed context.heap value actual
  rw [body_shape] at actual
  obtain ⟨positive,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post ch "mark" kind.afterMark context.heap
    (HeapScope.mark_original_code source.code context.installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" ch
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name ch different
  have next : MerkleMemory.Context entry ch zeros query := ⟨context.installed,context.domain,context.zeroCell,context.zeroArena,context.heap,context.heapLower,context.heapBound,context.aligned,context.below⟩
  have memory := after_mark_memory kind entry inner p ch out zeros query next ((kept kind.inputName (by cases kind <;> decide)).trans pointer)
    ((kept "out" (by decide)).trans output) inputArena outArena outAway value remaining
  refine ⟨?_,heap⟩
  rw [endpoint]
  exact memory

theorem call_frame (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out zeros query : BitVec 64)
    (context : MerkleMemory.Context source ch zeros query)
    (inputArena : AllocatedBytes.Arena p kind.length) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (scalarValues p out))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) kind.name arguments)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)) := by
  obtain ⟨callee,called,pointer,output⟩ := word_pair_environment source.code.lookup kind.name (ofString kind.inputName) (ofString "out") kind.body .one p out
    (by cases kind <;> decide) (original_code kind source.code context.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post kind.name arguments actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have image := body_frame kind (callEntryStateHOLFinite source callee) target p ch out zeros query (context.at_callee callee) pointer output inputArena outArena outAway returned bodyRun
  rw [endpoint]
  exact image

end InitECandidate.Solver.Input.CurrentHash.FixedRecord

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.after_steps_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.after_allocation_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.body_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.call_frame
