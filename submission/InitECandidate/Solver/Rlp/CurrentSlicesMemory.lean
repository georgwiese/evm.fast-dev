import InitECandidate.Solver.Rlp.CurrentSlicesAfterCountNormal
import InitECandidate.Solver.Rlp.CurrentListCount.ItemsCall
import InitECandidate.Solver.Rlp.CurrentSlicesCost
import InitECandidate.Solver.Rlp.SlicesWindowBytes

namespace InitECandidate.Solver.Rlp.CurrentSlices
open Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- Actual normal current conversion derives the complete input item sequence,
exact stored record count, real allocation room and heap update. Scratch work and the fresh array retain every earlier physical input word;
normal runtime metadata includes the real heap update. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ items : List ListItem,∃ count : BitVec 64,
      ListItems target pointer length.toNat items ∧ count.toNat=items.length ∧ count.toNat≤length.toNat ∧
      value=Slices.result heap count ∧ Records target.memory heap pointer items ∧ heap.toNat+16*count.toNat≤2952790016 ∧
      CurrentStartup.ArenaState target ∧
      target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64)))) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat→target.memory query=source.memory query) ∧
      MemoryMetadata.erase target=MemoryMetadata.erase (PersistentAlloc.post source heap (count*16#64)) ∧
      source.clock-target.clock≤71*length.toNat+3 := by
  have fits : pointer.toNat+length.toNat<2^64 := by have h:=heap.isLt; omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  obtain ⟨items,count,countPost,inner,itemModel,countEq,clockBound,price,countMetadata,countOutside,continuation,restored⟩ :=
    CurrentListCount.scoped_normal_items source target pointer length arena fits (by omega) "count" arguments afterCount args value
      (by rw [←body_shape]; exact normal)
  let ready := bind {countPost with locals:=source.locals} "count" count
  have countGlobals := congrArg PanSemStateFiniteExact.globals countMetadata
  change countPost.globals=source.globals at countGlobals
  have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by
    change countPost.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
    rw [countGlobals]
    exact heapGlobal
  have countBytes := Validation.Outside.bytes_agree_below source countPost 2952790016 2965299200 pointer length countOutside fits (by omega)
  have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ "count" "p" _ (by decide)).trans pointerCell
  have readyCount : ready.locals.lookup (ofString "count")=some (.val (.word count)) := bind_lookup_same _ _ _
  have readyItems:=ListItems.transport source ready pointer length.toNat items itemModel length.isLt countBytes
  obtain ⟨room,answer,records,globals,frame,metadata⟩ := after_count_normal ready inner pointer length heap count items readyPointer readyCount readyItems countEq readyHeap heapBound before sizeBound (by change OriginalCode.Installed countPost.code; rw [MemoryMetadata.code countMetadata]; exact arena.code) value continuation
  have fields:=evaluation_fields ready inner afterCount (some (.returned value)) continuation
  have inputFrame:=Window.bytes_before ready inner heap.toNat (heap.toNat+16*count.toNat) pointer length frame before fits fields.1 fields.2.1
  have innerItems:=ListItems.transport ready inner pointer length.toNat items readyItems length.isLt inputFrame
  have finalItems:=ListItems.transport inner target pointer length.toNat items innerItems length.isLt (by intro offset inside; rw [restored]; rfl)
  have finalGlobals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64)))) := by
    rw [restored]
    exact globals.trans (congrArg (fun stateGlobals=>stateGlobals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64))))) countGlobals)
  have inherited := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    PersistentAlloc.post state heap (count*16#64)) countMetadata
  change MemoryMetadata.erase (PersistentAlloc.post ready heap (count*16#64))=
    MemoryMetadata.erase (PersistentAlloc.post source heap (count*16#64)) at inherited
  have finalFields:=evaluation_fields source target body (some (.returned value)) normal
  have finalArena : CurrentStartup.ArenaState target := by
    refine ⟨?_,?_,finalFields.1.trans arena.domain,?_⟩
    · rw [finalGlobals]
      simpa [HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide] using arena.scratch
    · rw [finalGlobals]
      simpa [HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.frame
    · rw [finalFields.2.2.2]; exact arena.code
  have countBound:=ListItems.count_le source pointer length.toNat items itemModel
  rw [←countEq] at countBound
  have priced:=body_cost source pointer length pointerCell lengthCell arena fits arena.code
  rw [normal] at priced
  refine ⟨items,count,finalItems,countEq,countBound,answer,?_,room,finalArena,finalGlobals,?_,?_,priced⟩
  · rw [restored]; exact records
  · intro query earlier
    rw [restored]
    exact (frame query (Or.inl earlier)).trans (countOutside query (Or.inl (Nat.lt_of_lt_of_le earlier heapBound)))
  · rw [restored]
    exact metadata.trans inherited

end InitECandidate.Solver.Rlp.CurrentSlices

#print axioms InitECandidate.Solver.Rlp.CurrentSlices.body_normal
