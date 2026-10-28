import InitECandidate.Solver.Input.CurrentHash.RootPipelineCost

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}

theorem State.tail_memory (state : State input source blob si record rq root array ch cursor length start size)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (outAway : CopyGeneral.Away root query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterLists=(some (.returned value),post)) : post.memory query=source.memory query := by
  unfold afterLists at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "merkleize") merkleArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := MerkleMemory.call_memory source middle ch 4#64 4#64 root cursor WorkspaceEntry.zeroPointer query 2 (state.context query before) (by decide) (by decide) (by decide)
    state.chunksArena state.data.rootArena outAway merkleArguments state.merkle_arguments normal
  have installed : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact state.data.workspace.code
  exact (HeapScope.release_return_memory middle post [localVar "mark"] query installed value remaining).trans frame

/-- Complete actual four-field root pipeline and final Merkle/release keep
arbitrary protected earlier metadata, with the same decoded images and heap
reconstituted after each real normal child call. -/
theorem pipeline_memory (items : List Step) (state : State input source blob si record rq root array ch cursor length start size)
    (query : BitVec 64) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away WorkspaceEntry.chunkPointer query 32) (outAway : CopyGeneral.Away root query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source (pipeline items afterLists)=(some (.returned value),post)) : post.memory query=source.memory query := by
  induction items generalizing source with
  | nil=>exact state.tail_memory query before outAway value actual
  | cons item rest ih=>
    change evaluateHOLFiniteState source (.seq item.call (pipeline rest afterLists))=(some (.returned value),post) at actual
    have safe : LocalPrefix (ofString "out") item.call := .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
    have front := state.call_frame (post:=middle) item query before chunkAway normal
    have next := state.after_call (post:=middle) item normal
    exact (ih next remaining).trans front.1

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.tail_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.pipeline_memory
