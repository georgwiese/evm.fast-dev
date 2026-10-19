import InitECandidate.Solver.Rlp.SlicesNormal

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_list_to_slices") arguments continuation)=(some (.returned returned),post)) :
    1≤source.clock ∧ ∃ calleePost items count inner,
      ListItems calleePost pointer length.toNat items ∧ count.toNat=items.length ∧ count.toNat≤length.toNat ∧
      Records calleePost.memory heap pointer items ∧ heap.toNat+16*count.toNat≤33806089496 ∧
      Validation.Arena calleePost cursor limit ∧ calleePost.code=source.code ∧
      calleePost.memaddrs=source.memaddrs ∧ calleePost.be=source.be ∧
      calleePost.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (count*16#64)))) ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+16*count.toNat≤query.toNat →
        calleePost.memory query=source.memory query) ∧ source.clock-calleePost.clock≤71*length.toNat+35 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source calleePost name (result heap count)) continuation=(some (.returned returned),inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code installed)
  obtain ⟨positive,calleePost,value,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_normal source post name resultShape (ofString "rlp_list_to_slices") arguments _ body continuation callee resultShape args called returned normal
  obtain ⟨items,count,itemModel,countEq,countBound,answer,records,room,nextArena,nextHeap,frame,price⟩ :=
    body_normal (callEntryStateHOLFinite source callee) calleePost pointer length heap cursor limit cutoff pointerLocal lengthLocal
      (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove installed value bodyRun
  rw [answer] at continuationRun
  have fields := Input.evaluation_fields (callEntryStateHOLFinite source callee) calleePost body (some (.returned value)) bodyRun
  have clock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤71*length.toNat+34 at price
  exact ⟨positive,calleePost,items,count,inner,itemModel,countEq,countBound,records,room,nextArena,fields.2.2.2,fields.1,fields.2.1,nextHeap,frame,by omega,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.scoped_normal
