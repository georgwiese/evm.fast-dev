import InitECandidate.Solver.Input.CurrentHash.PayloadStateCalls
import InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem State.with_context (data : State input source blob record array ch cursor chunk out zeros length start size) (nextCursor : BitVec 64)
    (context : MerkleMemory.Context post nextCursor zeros record) (afterChunks : ch.toNat+608≤nextCursor.toNat)
    (memory : ∀ query : BitVec 64,record.toNat≤query.toNat → query.toNat<ch.toNat → post.memory query=source.memory query)
    (payload : post.locals.lookup (ofString "pl")=some (.val (.word record))) (raw : post.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64))))
    (chunks : post.locals.lookup (ofString "ch")=some (.val (.word ch))) (output : post.locals.lookup (ofString "out")=some (.val (.word out)))
    (chunkCell : post.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))) :
    State input post blob record array ch nextCursor chunk out zeros length start size := by
  have heap : NormalHeapEffects.AtLeast (array.toNat+16*VarList.decodedCount input start size) post :=
    ⟨nextCursor,context.heap,by have h:=data.afterArray; omega,context.heapBound,context.aligned⟩
  have image := data.decoded.of_interval ch.toNat data.afterArray memory heap
  exact ⟨context,image,data.inputBound,data.inputArena,data.recordArena,data.recordAligned,payload,raw,chunks,output,data.chunksArena,data.chunksAligned,
    data.afterRecord,data.afterArray,afterChunks,chunkCell,data.chunkArena,data.chunkAligned,data.chunkBefore⟩

/-- Pure local scope entries keep the same physical decoded image and heap.
Only the four actual parent bindings need be retained. -/
theorem State.of_frame (data : State input source blob record array ch cursor chunk out zeros length start size)
    (frame : LocalEffects.erase post=LocalEffects.erase source)
    (payload : post.locals.lookup (ofString "pl")=some (.val (.word record))) (raw : post.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64))))
    (chunks : post.locals.lookup (ofString "ch")=some (.val (.word ch))) (output : post.locals.lookup (ofString "out")=some (.val (.word out))) :
    State input post blob record array ch cursor chunk out zeros length start size := by
  have context := data.context.of_frozen frame
  have globals := congrArg PanSemStateFiniteExact.globals frame
  change post.globals=source.globals at globals
  have chunkCell := (congrArg (fun table=>table.lookup (ofString "ssz_len_chunk")) globals).trans data.chunkCell
  exact ⟨context,data.decoded.of_frame frame,data.inputBound,data.inputArena,data.recordArena,data.recordAligned,payload,raw,chunks,output,
    data.chunksArena,data.chunksAligned,data.afterRecord,data.afterArray,data.afterChunks,chunkCell,data.chunkArena,data.chunkAligned,data.chunkBefore⟩

theorem State.at_clock (data : State input source blob record array ch cursor chunk out zeros length start size) (clock : Nat) :
    State input {source with clock:=clock} blob record array ch cursor chunk out zeros length start size :=
  data.of_frame rfl data.payload data.raw data.chunks data.output

theorem State.bound (data : State input source blob record array ch cursor chunk out zeros length start size) (name : String) (word : BitVec 64)
    (different : ofString name≠ofString "pl" ∧ ofString name≠ofString "raw" ∧ ofString name≠ofString "ch" ∧ ofString name≠ofString "out") :
    State input (bind source name word) blob record array ch cursor chunk out zeros length start size :=
  data.of_frame rfl ((bind_lookup_other source name "pl" word different.1).trans data.payload)
    ((bind_lookup_other source name "raw" word different.2.1).trans data.raw)
    ((bind_lookup_other source name "ch" word different.2.2.1).trans data.chunks)
    ((bind_lookup_other source name "out" word different.2.2.2).trans data.output)

/-- Actual allocator return changes the frontier and caller local while
preserving the complete earlier payload and its real root/chunk geometry. -/
theorem State.allocated (data : State input source blob record array ch cursor chunk out zeros length start size) (amount : BitVec 64)
    (room : cursor.toNat+amount.toNat≤2952790016)
    (same : LocalEffects.erase post=LocalEffects.erase (PersistentAlloc.post source cursor amount)) :
    State input (CallNormal.continuationEntry source post "roots" (.val (.word cursor))) blob record array ch (PersistentAlloc.rounded cursor amount) chunk out zeros length start size := by
  let entry := CallNormal.continuationEntry source post "roots" (.val (.word cursor))
  let expected := MemoryContextAllocation.entry source cursor amount "roots"
  have context := MemoryContextAllocation.context source cursor amount zeros record "roots" data.context room
  have frame : CeilLog2.frozen entry=CeilLog2.frozen expected := same
  have nextContext : MerkleMemory.Context entry (PersistentAlloc.rounded cursor amount) zeros record := context.of_frozen frame
  have memory : entry.memory=source.memory := LocalEffects.memory_of_erase (PersistentAlloc.post source cursor amount) post same
  have kept (name : String) (different : ofString "roots"≠ofString name) := CallNormal.continuation_lookup_other source post "roots" name (.val (.word cursor)) different
  have guards := PersistentAlloc.guards cursor amount room
  have globals := congrArg PanSemStateFiniteExact.globals same
  change post.globals=(source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor amount)))) at globals
  have chunkCell : entry.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)) := by
    change post.globals.lookup (ofString "ssz_len_chunk")=_
    rw [globals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "heap_ptr"≠ofString "ssz_len_chunk" from by decide] using data.chunkCell
  exact data.with_context _ nextContext (by have h:=data.afterChunks; have g:=guards.2.2.1; omega)
    (by intro query lower upper; exact congrFun memory query) ((kept "pl" (by decide)).trans data.payload) ((kept "raw" (by decide)).trans data.raw)
    ((kept "ch" (by decide)).trans data.chunks) ((kept "out" (by decide)).trans data.output) chunkCell

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.with_context
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.of_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.at_clock
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.bound
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.allocated
