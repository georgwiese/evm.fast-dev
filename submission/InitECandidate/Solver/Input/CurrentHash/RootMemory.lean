import InitECandidate.Solver.Input.CurrentHash.RootPipelineMemory
import InitECandidate.Solver.Input.CurrentHash.RootCost

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob si record rq root array : BitVec 64} {length start size : Nat}

theorem after_mark_memory (data : Invocation.Data input source blob si record rq root array length start size) (cursor : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) (rootBefore : root.toNat+32≤cursor.toNat)
    (bounded : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (query : BitVec 64) (before : query.toNat<cursor.toNat) (chunkAway : CopyGeneral.Away WorkspaceEntry.chunkPointer query 32) (outAway : CopyGeneral.Away root query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [source_shape.2.1] at actual
  obtain ⟨room,funded,inner,remaining,endpoint⟩ := PersistentAlloc.call_normal source post "ch" [.panop .mul [.const 4#64,.const 32#64]] afterAllocation cursor 128#64 rfl
    (PersistentAlloc.original_code source.code data.workspace.code) (Trap.original_code source.code data.workspace.code) heap bounded value actual
  let target := PersistentAlloc.post {source with clock:=source.clock-1} cursor 128#64
  have next := allocated (target:=target) data rootBefore bounded aligned room rfl
  rw [source_shape.2.2] at remaining
  have frame := pipeline_memory (post:=inner) steps next query before chunkAway outAway value remaining
  rw [endpoint]
  exact frame

/-- Complete unchanged current root-hash body retains earlier protected
caller metadata and restores its entering heap, on the same normal return.
The exact main decoder, actual allocations and each real child return supply
all metadata/heap transitions; there is no assumed future successful hash. -/
theorem body_frame (data : Invocation.Data input source blob si record rq root array length start size) (cursor : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (query : BitVec 64) (before : query.toNat<cursor.toNat) (chunkAway : CopyGeneral.Away WorkspaceEntry.chunkPointer query 32) (outAway : CopyGeneral.Away root query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have restored := body_heap source post cursor data.workspace.code heap value actual
  obtain ⟨old,oldHeap,rootBefore,bounded,aligned⟩ := data.heap
  have equal : old=cursor := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using oldHeap.symm.trans heap
  subst old
  rw [source_shape.1] at actual
  obtain ⟨funded,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code data.workspace.code) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have next : Invocation.Data input entry blob si record rq root array length start size := (data.at_clock (source.clock-1)).bound "mark" cursor (by decide)
  have frame := after_mark_memory (post:=inner) next cursor heap rootBefore bounded aligned query before chunkAway outAway value remaining
  refine ⟨?_,restored⟩
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.body_frame
