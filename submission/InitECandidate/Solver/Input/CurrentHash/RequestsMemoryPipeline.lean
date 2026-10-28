import InitECandidate.Solver.Input.CurrentHash.RequestsState
import InitECandidate.Solver.Input.CurrentHash.PContainerMemory

namespace InitECandidate.Solver.Input.CurrentHash.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob rq ch cursor chunk out zeros : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}

theorem State.context_below (data : State input source blob rq ch cursor chunk out zeros start size counts) (query : BitVec 64) (below : query.toNat<ch.toNat) :
    MerkleMemory.Context source cursor zeros query := by
  refine ⟨data.context.installed,data.context.domain,data.context.zeroCell,data.context.zeroArena,data.context.heap,data.context.heapLower,data.context.heapBound,data.context.aligned,?_⟩
  have h:=data.afterChunks
  omega

theorem State.output_away_below (data : State input source blob rq ch cursor chunk out zeros start size counts) (kind : RequestList.Kind) (query : BitVec 64)
    (below : query.toNat<ch.toNat) : CopyGeneral.Away (ch+BitVec.ofNat 64 (32*kind.tag)) query 32 := by
  have index := kind_index kind
  have fits : ch.toNat+32*kind.tag<2^64 := by have h:=data.chunksArena.upper; omega
  have aligned : (ch+BitVec.ofNat 64 (32*kind.tag)).toNat%8=0 := byteAddress_aligned ch (32*kind.tag) data.chunksAligned (by omega) fits
  have arena := data.output_arena kind
  apply CopyGeneral.Away.after _ query 32 aligned (by have h:=arena.upper; omega)
  change query.toNat<(byteAddress ch (32*kind.tag)).toNat
  rw [byteAddress_toNat ch (32*kind.tag) fits]
  omega

theorem State.call_memory (data : State input source blob rq ch cursor chunk out zeros start size counts) (kind : RequestList.Kind) (query : BitVec 64)
    (below : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32)
    (actual : evaluateHOLFiniteState source (listCall kind)=(none,post)) : post.memory query=source.memory query := by
  have args := arguments_read source blob rq ch start size counts kind data.decoded data.context.domain data.request data.chunks
  exact (RequestList.call_frame source post kind (blob+BitVec.ofNat 64 start+Requests.offsetWord input start kind.tag) cursor chunk
    (ch+BitVec.ofNat 64 (32*kind.tag)) zeros query (counts kind.tag).toNat (data.context_below query below)
    (data.decoded.count_bound kind.tag (kind_index kind)) (input_arena data.decoded kind) (data.output_arena kind) (data.output_away_below kind query below)
    data.chunkCell data.chunkArena data.chunkAligned chunkAway (arguments kind) args actual).1

theorem State.tail_memory (data : State input source blob rq ch cursor chunk out zeros start size counts) (query : BitVec 64)
    (below : query.toNat<ch.toNat) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterLists=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "ch",.const 5#64,localVar "out"]=
      some [.val (.word ch),.val (.word 5#64),.val (.word out)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,data.chunks,data.output]
  unfold afterLists at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (Code.name .htr_pcontainer) [localVar "ch",.const 5#64,localVar "out"]) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have front := PContainer.call_frame source middle ch cursor out zeros query 5 (data.context_below query below) (by decide) data.chunksArena outAway _ args normal
  have installed : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact data.context.installed
  exact (HeapScope.release_return_memory middle post [localVar "mark"] query installed value remaining).trans front.1

/-- All five actual list calls and final container/release retain earlier
metadata outside the real output and length chunk, on this same normal return. -/
theorem pipeline_memory (kinds : List RequestList.Kind) {input : Guest.InputBlob}
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (blob rq ch cursor chunk out zeros query : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64)
    (data : State input source blob rq ch cursor chunk out zeros start size counts)
    (below : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (pipeline kinds afterLists)=(some (.returned value),post)) : post.memory query=source.memory query := by
  induction kinds generalizing source with
  | nil=>exact data.tail_memory query below outAway value actual
  | cons kind rest ih=>
    change evaluateHOLFiniteState source (.seq (listCall kind) (pipeline rest afterLists))=(some (.returned value),post) at actual
    have safe : LocalPrefix (ofString "out") (listCall kind) := .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
    have front := data.call_memory kind query below chunkAway normal
    have next := data.after_list kind normal
    exact (ih middle next remaining).trans front

end InitECandidate.Solver.Input.CurrentHash.RequestsHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.context_below
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.output_away_below
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.call_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.State.tail_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.pipeline_memory
