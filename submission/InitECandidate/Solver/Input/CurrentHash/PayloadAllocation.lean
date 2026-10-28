import InitECandidate.Solver.Input.CurrentHash.PayloadStateTransport

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual payload body entry, before its nineteen-chunk allocation. All
physical decoder/workspace/frontier facts must come from the real root caller. -/
structure Before (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob record array cursor chunk out zeros : BitVec 64) (length start size : Nat) : Prop where
  context : MerkleMemory.Context source cursor zeros record
  decoded : Payload.ReturnedImage input source blob record array length start size
  inputBound : input.length%2^64≤251655056
  inputArena : AllocatedBytes.Arena blob (input.length%2^64)
  recordArena : AllocatedBytes.Arena record 136
  recordAligned : record.toNat%8=0
  payload : source.locals.lookup (ofString "pl")=some (.val (.word record))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))
  recordBefore : record.toNat+136≤cursor.toNat
  arrayBefore : array.toNat+16*VarList.decodedCount input start size≤cursor.toNat
  chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))
  chunkArena : AllocatedBytes.Arena chunk 32
  chunkAligned : chunk.toNat%8=0
  chunkBefore : chunk.toNat+32≤record.toNat

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem Before.of_frame (data : Before input source blob record array cursor chunk out zeros length start size)
    (frame : LocalEffects.erase post=LocalEffects.erase source)
    (payload : post.locals.lookup (ofString "pl")=some (.val (.word record))) (output : post.locals.lookup (ofString "out")=some (.val (.word out))) :
    Before input post blob record array cursor chunk out zeros length start size := by
  have globals := congrArg PanSemStateFiniteExact.globals frame
  change post.globals=source.globals at globals
  exact ⟨data.context.of_frozen frame,data.decoded.of_frame frame,data.inputBound,data.inputArena,data.recordArena,data.recordAligned,payload,output,
    data.recordBefore,data.arrayBefore,(congrArg (fun table=>table.lookup (ofString "ssz_len_chunk")) globals).trans data.chunkCell,data.chunkArena,data.chunkAligned,data.chunkBefore⟩

theorem Before.at_clock (data : Before input source blob record array cursor chunk out zeros length start size) (clock : Nat) :
    Before input {source with clock:=clock} blob record array cursor chunk out zeros length start size := data.of_frame rfl data.payload data.output

theorem Before.bound (data : Before input source blob record array cursor chunk out zeros length start size) (name : String) (word : BitVec 64)
    (different : ofString name≠ofString "pl" ∧ ofString name≠ofString "out") : Before input (bind source name word) blob record array cursor chunk out zeros length start size :=
  data.of_frame rfl ((bind_lookup_other source name "pl" word different.1).trans data.payload) ((bind_lookup_other source name "out" word different.2).trans data.output)

theorem Before.raw_read (data : Before input source blob record array cursor chunk out zeros length start size) : eval source (fieldExpression 0)=some (.val (.word (blob+62#64))) := by
  have pointer : eval source (localVar "pl")=some (.val (.word record)) := by simpa [eval,evalHOLExact,toExact,localVar] using data.payload
  have cell : source.memory (record+BitVec.ofNat 64 0)=.word (blob+62#64) := by simpa only [BitVec.add_zero] using data.decoded.transactions.hashPrefix.raw
  exact Witness.load_word_read source _ _ _ (Scalar.plus_read source _ record 0 pointer)
    (AllocatedBytes.word_mapped source record 136 0 data.context.domain data.recordArena (by decide) data.recordAligned (by decide)) cell

/-- Only the same normal allocation return supplies the actual chunk extent
and next frontier. Earlier decoder data survives its real memory frame. -/
theorem Before.allocated (data : Before input source blob record array cursor chunk out zeros length start size)
    (raw : source.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64))))
    (room : cursor.toNat+608≤2952790016) (same : LocalEffects.erase post=LocalEffects.erase (PersistentAlloc.post source cursor 608#64)) :
    State input (CallNormal.continuationEntry source post "ch" (.val (.word cursor))) blob record array cursor (PersistentAlloc.rounded cursor 608#64) chunk out zeros length start size := by
  let entry := CallNormal.continuationEntry source post "ch" (.val (.word cursor))
  let expected := MemoryContextAllocation.entry source cursor 608#64 "ch"
  have context := MemoryContextAllocation.context source cursor 608#64 zeros record "ch" data.context room
  have frame : CeilLog2.frozen entry=CeilLog2.frozen expected := same
  have nextContext : MerkleMemory.Context entry (PersistentAlloc.rounded cursor 608#64) zeros record := context.of_frozen frame
  have memory : entry.memory=source.memory := LocalEffects.memory_of_erase (PersistentAlloc.post source cursor 608#64) post same
  have guards := PersistentAlloc.guards cursor 608#64 room
  have heap : NormalHeapEffects.AtLeast (array.toNat+16*VarList.decodedCount input start size) entry :=
    ⟨_,nextContext.heap,by have h:=data.arrayBefore; have g:=guards.2.2.1; omega,nextContext.heapBound,nextContext.aligned⟩
  have image := data.decoded.of_interval cursor.toNat data.arrayBefore (by intro query lower upper; exact congrFun memory query) heap
  have kept (name : String) (different : ofString "ch"≠ofString name) := CallNormal.continuation_lookup_other source post "ch" name (.val (.word cursor)) different
  have globals := congrArg PanSemStateFiniteExact.globals same
  change post.globals=(source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor 608#64)))) at globals
  have chunkCell : entry.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)) := by
    change post.globals.lookup (ofString "ssz_len_chunk")=_
    rw [globals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "heap_ptr"≠ofString "ssz_len_chunk" from by decide] using data.chunkCell
  exact ⟨nextContext,image,data.inputBound,data.inputArena,data.recordArena,data.recordAligned,(kept "pl" (by decide)).trans data.payload,
    (kept "raw" (by decide)).trans raw,CallNormal.continuation_lookup_same _ _ _ _,(kept "out" (by decide)).trans data.output,
    ⟨data.context.heapLower,by omega⟩,data.context.aligned,data.recordBefore,data.arrayBefore,guards.2.2.1,chunkCell,data.chunkArena,data.chunkAligned,data.chunkBefore⟩

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Before.of_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Before.bound
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Before.raw_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Before.allocated
