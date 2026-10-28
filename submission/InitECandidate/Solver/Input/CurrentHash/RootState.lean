import InitECandidate.Solver.Input.CurrentHash.RootProgram
import InitECandidate.Solver.Input.CurrentHash.Invocation
import InitECandidate.Solver.Input.CurrentHash.PayloadCallMemory
import InitECandidate.Solver.Input.CurrentHash.RequestsMemory

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Same-main-decoder root state after the actual128-byte chunk allocation.
Every physical payload/request/SI fact belongs to this current caller. -/
structure State (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob si record rq root array ch cursor : BitVec 64) (length start size : Nat) : Prop where
  data : Invocation.Data input source blob si record rq root array length start size
  chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))
  chunksArena : AllocatedBytes.Arena ch 128
  chunksAligned : ch.toNat%8=0
  chunksAfter : root.toNat+32≤ch.toNat
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))
  heapBound : cursor.toNat≤2952790016
  heapAligned : cursor.toNat%8=0
  heapAfter : ch.toNat+128≤cursor.toNat

variable {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}

theorem State.context (state : State input source blob si record rq root array ch cursor length start size) (query : BitVec 64) (before : query.toNat<ch.toNat) :
    MerkleMemory.Context source cursor WorkspaceEntry.zeroPointer query :=
  ⟨state.data.workspace.code,state.data.workspace.domain,state.data.workspace.zeros,state.data.workspace.zeroArena,state.heap,
    by have a:=state.chunksArena.lower; have b:=state.heapAfter; omega,state.heapBound,state.heapAligned,by have h:=state.heapAfter; omega⟩

theorem State.output_arena (state : State input source blob si record rq root array ch cursor length start size) (slot : Nat) (inside : slot<4) :
    AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*slot)) 32 := AllocatedBytes.Arena.subrange ch 128 (32*slot) 32 state.chunksArena (by omega)

theorem State.output_away (state : State input source blob si record rq root array ch cursor length start size) (slot : Nat) (inside : slot<4) (query : BitVec 64) (before : query.toNat<ch.toNat) :
    CopyGeneral.Away (ch+BitVec.ofNat 64 (32*slot)) query 32 := by
  have fits : ch.toNat+32*slot<2^64 := by have h:=state.chunksArena.upper; omega
  have aligned : (ch+BitVec.ofNat 64 (32*slot)).toNat%8=0 := byteAddress_aligned ch (32*slot) state.chunksAligned (by omega) fits
  have arena := state.output_arena slot inside
  apply CopyGeneral.Away.after _ _ 32 aligned (by have h:=arena.upper; omega)
  change query.toNat<(byteAddress ch (32*slot)).toNat
  rw [byteAddress_toNat ch (32*slot) fits]
  omega

theorem State.input_bounds (state : State input source blob si record rq root array ch cursor length start size) :
    input.length%2^64≤251655056 ∧ AllocatedBytes.Arena blob (input.length%2^64) ∧ 2701134824≤blob.toNat := by
  obtain ⟨requestStart,requestSize,counts,requests⟩ := state.data.requestImage
  exact ⟨requests.inputBound,requests.inputArena,requests.inputLower⟩

theorem State.chunk_before_si (state : State input source blob si record rq root array ch cursor length start size) : WorkspaceEntry.chunkPointer.toNat+32≤si.toNat := by
  have inputLower:=state.input_bounds.2.2
  have afterInput:=state.data.siAfterInput
  change 2701132496+32≤si.toNat
  omega

theorem State.payload_context (state : State input source blob si record rq root array ch cursor length start size) :
    MerkleMemory.Context source cursor WorkspaceEntry.zeroPointer record := by
  apply state.context record
  have a:=state.data.rootAfter; have b:=state.chunksAfter
  omega

theorem State.payload_frontier (state : State input source blob si record rq root array ch cursor length start size) :
    record.toNat+136≤cursor.toNat ∧ array.toNat+16*VarList.decodedCount input start size≤cursor.toNat ∧ WorkspaceEntry.chunkPointer.toNat+32≤record.toNat := by
  have a:=state.data.rootAfter; have b:=state.data.arrayBefore; have c:=state.chunksAfter; have d:=state.heapAfter
  have e:=state.chunk_before_si; have f:=state.data.payloadAfterSI
  exact ⟨by omega,by omega,by omega⟩

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.context
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.output_arena
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.output_away
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.input_bounds
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.chunk_before_si
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.payload_context
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.payload_frontier
