import InitECandidate.Solver.Rlp.CurrentSlicesMemory
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.CurrentSlices
open Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- The real scoped converter caller carries its actual allocated array,
count, validated input sequence and fresh-array frame into the continuation. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64)
    (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_list_to_slices") arguments continuation)=(some (.returned returned),post)) :
    1≤source.clock ∧ ∃ calleePost items count inner,
      ListItems calleePost pointer length.toNat items ∧ count.toNat=items.length ∧ count.toNat≤length.toNat ∧
      Records calleePost.memory heap pointer items ∧ heap.toNat+16*count.toNat≤2952790016 ∧
      CurrentStartup.ArenaState calleePost ∧ calleePost.memaddrs=source.memaddrs ∧ calleePost.be=source.be ∧
      calleePost.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64)))) ∧
      Window source calleePost heap.toNat (heap.toNat+16*count.toNat) ∧
      MemoryMetadata.erase calleePost=MemoryMetadata.erase (PersistentAlloc.post source heap (count*16#64)) ∧
      calleePost.clock≤source.clock ∧ source.clock-calleePost.clock≤57*length.toNat+4 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source calleePost name (Slices.result heap count)) continuation=(some (.returned returned),inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code arena.code)
  obtain ⟨positive,calleePost,value,inner,bodyRun,checked,continuationRun,restored⟩ :=
    CallNormal.scoped_normal source post name resultShape (ofString "rlp_list_to_slices") arguments (Header.values pointer length) body continuation callee resultShape args called returned normal
  obtain ⟨items,count,itemModel,countEq,countBound,answer,records,room,nextArena,globals,frame,metadata,price⟩ :=
    body_normal (callEntryStateHOLFinite source callee) calleePost pointer length heap pointerLocal lengthLocal
      (arena.of_frame rfl) heapGlobal heapBound before sizeBound value bodyRun
  rw [answer] at continuationRun
  have fields:=evaluation_fields (callEntryStateHOLFinite source callee) calleePost body (some (.returned value)) bodyRun
  have clock:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤57*length.toNat+3 at price
  exact ⟨positive,calleePost,items,count,inner,itemModel,countEq,countBound,records,room,nextArena,fields.1,fields.2.1,globals,frame,metadata,(by omega),(by omega),continuationRun,restored⟩

end InitECandidate.Solver.Rlp.CurrentSlices

#print axioms InitECandidate.Solver.Rlp.CurrentSlices.scoped_normal
