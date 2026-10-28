import InitECandidate.Solver.Input.CurrentHash.RootInputGeometry

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}

theorem metadata_chunk_away (query : BitVec 64) (lower : 2701134640≤query.toNat) : CopyGeneral.Away WorkspaceEntry.chunkPointer query 32 :=
  CopyGeneral.Away.before WorkspaceEntry.chunkPointer query 32 2701134640 (by decide) (by decide) lower

theorem State.record_lower (state : State input source blob si record rq root array ch cursor length start size) : 2701134640≤record.toNat := by
  have a:=state.input_bounds.2.2; have b:=state.data.siAfterInput; have c:=state.data.payloadAfterSI
  omega

theorem State.record_before_chunks (state : State input source blob si record rq root array ch cursor length start size) : record.toNat<ch.toNat := by
  have a:=state.data.rootAfter; have b:=state.chunksAfter
  omega

theorem State.requests_context (state : State input source blob si record rq root array ch cursor length start size) : MerkleMemory.Context source cursor WorkspaceEntry.zeroPointer rq := by
  apply state.context rq
  have a:=state.data.rootAfter; have b:=state.chunksAfter
  omega

theorem State.requests_frontier (state : State input source blob si record rq root array ch cursor length start size) :
    rq.toNat+80≤cursor.toNat ∧ WorkspaceEntry.chunkPointer.toNat+32≤rq.toNat := by
  obtain ⟨requestStart,requestSize,counts,requests⟩ := state.data.requestImage
  have a:=state.data.rootAfter; have b:=state.chunksAfter; have c:=state.heapAfter
  have d:=requests.inputLower; have e:=requests.cursorAfterInput
  refine ⟨by omega,?_⟩
  change 2701132496+32≤rq.toNat
  omega

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.metadata_chunk_away
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.record_lower
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.record_before_chunks
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.requests_context
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.requests_frontier
