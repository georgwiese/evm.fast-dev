import InitECandidate.Solver.Input.CurrentHash.RequestsEntry
import InitECandidate.Solver.Input.CurrentHash.RequestListMemory

namespace InitECandidate.Solver.Input.CurrentHash.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Physical decoded fields and actual parent allocation at the next list
call. All facts concern this same current caller state and heap cursor. -/
structure State (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq ch cursor chunk out zeros : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64) : Prop where
  context : MerkleMemory.Context source cursor zeros rq
  decoded : Requests.DecodedImage input source blob rq start size counts
  request : source.locals.lookup (ofString "rq")=some (.val (.word rq))
  chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))
  chunksArena : AllocatedBytes.Arena ch 160
  chunksAligned : ch.toNat%8=0
  afterRecord : rq.toNat+80≤ch.toNat
  afterChunks : ch.toNat+160≤cursor.toNat
  chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))
  chunkArena : AllocatedBytes.Arena chunk 32
  chunkAligned : chunk.toNat%8=0
  chunkBefore : chunk.toNat+32≤rq.toNat

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob rq ch cursor chunk out zeros : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}

theorem State.query_context (data : State input source blob rq ch cursor chunk out zeros start size counts) (offset : Nat) (inside : offset<80) :
    MerkleMemory.Context source cursor zeros (rq+BitVec.ofNat 64 offset) := by
  have number := byteAddress_toNat rq offset (by have h:=data.decoded.cursorRoom; omega)
  refine ⟨data.context.installed,data.context.domain,data.context.zeroCell,data.context.zeroArena,data.context.heap,data.context.heapLower,data.context.heapBound,data.context.aligned,?_⟩
  change (byteAddress rq offset).toNat<cursor.toNat
  rw [number]
  have a:=data.afterRecord; have b:=data.afterChunks
  omega

theorem State.chunk_away (data : State input source blob rq ch cursor chunk out zeros start size counts) (offset : Nat) (inside : offset<80) :
    CopyGeneral.Away chunk (rq+BitVec.ofNat 64 offset) 32 := by
  apply CopyGeneral.Away.before chunk _ 32 rq.toNat data.chunkBefore rq.isLt
  change rq.toNat≤(byteAddress rq offset).toNat
  rw [byteAddress_toNat rq offset (by have h:=data.decoded.cursorRoom; omega)]
  omega

theorem State.output_arena (data : State input source blob rq ch cursor chunk out zeros start size counts) (kind : RequestList.Kind) :
    AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*kind.tag)) 32 :=
  AllocatedBytes.Arena.subrange ch 160 (32*kind.tag) 32 data.chunksArena (by have h:=kind_index kind; omega)

theorem State.output_away (data : State input source blob rq ch cursor chunk out zeros start size counts) (kind : RequestList.Kind) (offset : Nat) (inside : offset<80) :
    CopyGeneral.Away (ch+BitVec.ofNat 64 (32*kind.tag)) (rq+BitVec.ofNat 64 offset) 32 := by
  have index := kind_index kind
  have fits : ch.toNat+32*kind.tag<2^64 := by have h:=data.chunksArena.upper; omega
  have aligned : (ch+BitVec.ofNat 64 (32*kind.tag)).toNat%8=0 := byteAddress_aligned ch (32*kind.tag) data.chunksAligned (by omega) fits
  have arena := data.output_arena kind
  apply CopyGeneral.Away.after _ _ 32 aligned (by have h:=arena.upper; omega)
  change (byteAddress rq offset).toNat<(byteAddress ch (32*kind.tag)).toNat
  rw [byteAddress_toNat rq offset (by have h:=data.decoded.cursorRoom; omega),byteAddress_toNat ch (32*kind.tag) fits]
  have h:=data.afterRecord
  omega

/-- This actual list call retains any physical RQ field and restores the
current heap, using its same decoded count, physical slice and output slot. -/
theorem State.call_field_frame (data : State input source blob rq ch cursor chunk out zeros start size counts) (kind : RequestList.Kind) (offset : Nat) (inside : offset<80)
    (actual : evaluateHOLFiniteState source (listCall kind)=(none,post)) :
    post.memory (rq+BitVec.ofNat 64 offset)=source.memory (rq+BitVec.ofNat 64 offset) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have args := arguments_read source blob rq ch start size counts kind data.decoded data.context.domain data.request data.chunks
  exact RequestList.call_frame source post kind (blob+BitVec.ofNat 64 start+Requests.offsetWord input start kind.tag) cursor chunk
    (ch+BitVec.ofNat 64 (32*kind.tag)) zeros (rq+BitVec.ofNat 64 offset) (counts kind.tag).toNat (data.query_context offset inside)
    (data.decoded.count_bound kind.tag (kind_index kind)) (input_arena data.decoded kind) (data.output_arena kind) (data.output_away kind offset inside)
    data.chunkCell data.chunkArena data.chunkAligned (data.chunk_away offset inside) (arguments kind) args actual

/-- A genuine continuing parent call derives the next complete RQ image;
no later list success, count validity or separate execution is assumed. -/
theorem State.after_list (data : State input source blob rq ch cursor chunk out zeros start size counts) (kind : RequestList.Kind)
    (actual : evaluateHOLFiniteState source (listCall kind)=(none,post)) : State input post blob rq ch cursor chunk out zeros start size counts := by
  have heap := (data.call_field_frame kind 0 (by decide) actual).2
  have context := data.context.after_call .htr_request_list (arguments kind) heap actual
  have image := data.decoded.of_memory (by intro index inside; exact
    ⟨(data.call_field_frame kind (16*index) (by omega) actual).1,(data.call_field_frame kind (16*index+8) (by omega) actual).1⟩)
  have kept (name : String) := CallNormal.ignored_lookup source post (ofString name) (Code.name .htr_request_list) (arguments kind) actual
  have global := Effects.call_preserves .lengthChunk source.code data.context.installed .htr_request_list (some none) (arguments kind) source rfl
  change GlobalEffects.erase (key .lengthChunk) (evaluateHOLFiniteState source (listCall kind)).2=_ at global
  rw [actual] at global
  exact ⟨context,image,(kept "rq").trans data.request,(kept "ch").trans data.chunks,(kept "out").trans data.output,data.chunksArena,data.chunksAligned,
    data.afterRecord,data.afterChunks,(congrArg Prod.snd global).trans data.chunkCell,data.chunkArena,data.chunkAligned,data.chunkBefore⟩

end InitECandidate.Solver.Input.CurrentHash.RequestsHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.query_context
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.chunk_away
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.output_arena
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.output_away
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.call_field_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.after_list
