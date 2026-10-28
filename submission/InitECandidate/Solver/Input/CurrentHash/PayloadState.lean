import InitECandidate.Solver.Input.CurrentHash.PayloadStaticMemory
import InitECandidate.Solver.Input.CurrentHash.PayloadDecodedBudget

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete current payload at a parent hashing phase. Allocation facts refer
to the actual chunk buffer and frontier, not hypothetical temporary capacity. -/
structure State (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob record array ch cursor chunk out zeros : BitVec 64) (length start size : Nat) : Prop where
  context : MerkleMemory.Context source cursor zeros record
  decoded : Payload.ReturnedImage input source blob record array length start size
  inputBound : input.length%2^64≤251655056
  inputArena : AllocatedBytes.Arena blob (input.length%2^64)
  recordArena : AllocatedBytes.Arena record 136
  recordAligned : record.toNat%8=0
  payload : source.locals.lookup (ofString "pl")=some (.val (.word record))
  raw : source.locals.lookup (ofString "raw")=some (.val (.word (blob+62#64)))
  chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))
  chunksArena : AllocatedBytes.Arena ch 608
  chunksAligned : ch.toNat%8=0
  afterRecord : record.toNat+136≤ch.toNat
  afterArray : array.toNat+16*VarList.decodedCount input start size≤ch.toNat
  afterChunks : ch.toNat+608≤cursor.toNat
  chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))
  chunkArena : AllocatedBytes.Arena chunk 32
  chunkAligned : chunk.toNat%8=0
  chunkBefore : chunk.toNat+32≤record.toNat

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem State.query_context (data : State input source blob record array ch cursor chunk out zeros length start size) (query : BitVec 64) (before : query.toNat<ch.toNat) :
    MerkleMemory.Context source cursor zeros query :=
  ⟨data.context.installed,data.context.domain,data.context.zeroCell,data.context.zeroArena,data.context.heap,
    data.context.heapLower,data.context.heapBound,data.context.aligned,by have h:=data.afterChunks; omega⟩

/-- Reconstitute the complete same-decoder image from an actual memory frame,
current heap context, restored caller locals and length-workspace global. -/
theorem State.after_memory (data : State input source blob record array ch cursor chunk out zeros length start size)
    (context : MerkleMemory.Context post cursor zeros record)
    (memory : ∀ query : BitVec 64,record.toNat≤query.toNat → query.toNat<ch.toNat → post.memory query=source.memory query)
    (locals : ∀ name,post.locals.lookup name=source.locals.lookup name)
    (chunkCell : post.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))) :
    State input post blob record array ch cursor chunk out zeros length start size := by
  have heap : NormalHeapEffects.AtLeast (array.toNat+16*VarList.decodedCount input start size) post :=
    ⟨cursor,context.heap,by have a:=data.afterArray; have b:=data.afterChunks; omega,context.heapBound,context.aligned⟩
  have image := data.decoded.of_interval ch.toNat data.afterArray memory heap
  exact ⟨context,image,data.inputBound,data.inputArena,data.recordArena,data.recordAligned,(locals _).trans data.payload,(locals _).trans data.raw,
    (locals _).trans data.chunks,(locals _).trans data.output,data.chunksArena,data.chunksAligned,data.afterRecord,data.afterArray,data.afterChunks,
    chunkCell,data.chunkArena,data.chunkAligned,data.chunkBefore⟩

/-- Normal fixed-field calls derive the next complete payload state before
later literal field reads; their output bytes need not be known. -/
theorem State.after_static (data : State input source blob record array ch cursor chunk out zeros length start size)
    (fields : List StaticFields.Field) (members : ∀ field∈fields,field∈StaticFields.firstFields++StaticFields.middleFields++StaticFields.lastFields)
    (actual : evaluateHOLFiniteState source (StaticFields.program fields .skip)=(none,post)) :
    State input post blob record array ch cursor chunk out zeros length start size := by
  have rawArena := raw_arena data.decoded data.inputBound data.inputArena
  have valid : ∀ field∈fields,field.Valid := by intro field member; exact (StaticFields.fields_valid field (members field member)).1
  have frame (query : BitVec 64) (before : query.toNat<ch.toNat) := StaticFields.program_frame fields source post (blob+62#64) ch cursor zeros query
    valid (data.query_context query before) data.raw data.chunks
    (by intro field member; exact StaticFields.fields_geometry _ _ _ field (members field member) rawArena data.chunksArena data.chunksAligned before) actual
  have atRecord := frame record (by have h:=data.afterRecord; omega)
  have globals := StaticFields.program_globals .lengthChunk source.code data.context.installed fields source rfl
  rw [actual] at globals
  apply data.after_memory atRecord.2 (by intro query lower before; exact (frame query before).1) _ ((congrArg Prod.snd globals).trans data.chunkCell)
  intro name
  have summary := (StaticFields.program_local fields name).summary_full source
  unfold LocalSummary at summary
  rw [actual] at summary
  exact summary.1 rfl

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.query_context
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_static
