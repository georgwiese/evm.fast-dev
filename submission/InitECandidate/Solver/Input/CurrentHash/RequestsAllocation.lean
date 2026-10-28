import InitECandidate.Solver.Input.CurrentHash.RequestsState
import InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentHash.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual parent entry facts before its chunk allocation. The root caller
must derive these from its own decoded image and current allocation frontier. -/
structure Before (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq cursor chunk out zeros : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64) : Prop where
  context : MerkleMemory.Context source cursor zeros rq
  decoded : Requests.DecodedImage input source blob rq start size counts
  request : source.locals.lookup (ofString "rq")=some (.val (.word rq))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))
  recordBefore : rq.toNat+80≤cursor.toNat
  chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))
  chunkArena : AllocatedBytes.Arena chunk 32
  chunkAligned : chunk.toNat%8=0
  chunkBefore : chunk.toNat+32≤rq.toNat

/-- The same actual allocator return supplies the complete next parent state.
Its room and nonlocal frame come from AllocationScopeCost's real callee. -/
theorem Before.allocated {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob rq cursor chunk out zeros : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (data : Before input source blob rq cursor chunk out zeros start size counts)
    (room : cursor.toNat+160≤2952790016)
    (same : LocalEffects.erase target=LocalEffects.erase (PersistentAlloc.post source cursor 160#64)) :
    State input (CallNormal.continuationEntry source target "ch" (.val (.word cursor))) blob rq cursor (PersistentAlloc.rounded cursor 160#64) chunk out zeros start size counts := by
  let entry := CallNormal.continuationEntry source target "ch" (.val (.word cursor))
  let expected := MemoryContextAllocation.entry source cursor 160#64 "ch"
  have context := MemoryContextAllocation.context source cursor 160#64 zeros rq "ch" data.context room
  have frame : CeilLog2.frozen entry=CeilLog2.frozen expected := same
  have nextContext : MerkleMemory.Context entry (PersistentAlloc.rounded cursor 160#64) zeros rq := context.of_frozen frame
  have memory : entry.memory=source.memory := LocalEffects.memory_of_erase (PersistentAlloc.post source cursor 160#64) target same
  have image : Requests.DecodedImage input entry blob rq start size counts := data.decoded.of_memory
    (by intro index inside; exact ⟨congrFun memory _,congrFun memory _⟩)
  have request := (CallNormal.continuation_lookup_other source target "ch" "rq" (.val (.word cursor)) (by decide)).trans data.request
  have output := (CallNormal.continuation_lookup_other source target "ch" "out" (.val (.word cursor)) (by decide)).trans data.output
  have chunks := CallNormal.continuation_lookup_same source target "ch" (.val (.word cursor))
  have arena : AllocatedBytes.Arena cursor 160 := ⟨data.context.heapLower,by omega⟩
  have guards := PersistentAlloc.guards cursor 160#64 room
  have globals := congrArg PanSemStateFiniteExact.globals same
  change target.globals=(source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor 160#64)))) at globals
  have chunkCell : entry.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)) := by
    change target.globals.lookup (ofString "ssz_len_chunk")=_
    rw [globals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "heap_ptr"≠ofString "ssz_len_chunk" from by decide] using data.chunkCell
  exact ⟨nextContext,image,request,chunks,output,arena,data.context.aligned,data.recordBefore,guards.2.2.1,chunkCell,data.chunkArena,data.chunkAligned,data.chunkBefore⟩

end InitECandidate.Solver.Input.CurrentHash.RequestsHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.Before.allocated
