import InitECandidate.Solver.Rlp.CurrentSlicesAfterCountNormal
import InitECandidate.Solver.Rlp.CurrentListCount.ItemsCall
import InitECandidate.Solver.Rlp.CurrentSlicesCost
import InitECandidate.Solver.Rlp.SlicesWindowBytes

namespace InitECandidate.Solver.Rlp.CurrentSlices
open Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- Actual normal current conversion derives the complete input item sequence,
exact stored record count, real allocation room and heap update. The only
writes occur in that fresh array; no scratch cutoff is needed. -/
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
      Window source target heap.toNat (heap.toNat+16*count.toNat) ∧ source.clock-target.clock≤57*length.toNat+3 := by
  have fits : pointer.toNat+length.toNat<2^64 := by have h:=heap.isLt; omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  obtain ⟨items,count,clock,inner,itemModel,countEq,clockBound,price,continuation,restored⟩ :=
    CurrentListCount.scoped_normal_items source target pointer length arena fits "count" arguments afterCount args value
      (by rw [←body_shape]; exact normal)
  let ready := bind {source with clock:=clock} "count" count
  have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ "count" "p" _ (by decide)).trans pointerCell
  have readyCount : ready.locals.lookup (ofString "count")=some (.val (.word count)) := bind_lookup_same _ _ _
  have readyItems:=ListItems.transport source ready pointer length.toNat items itemModel length.isLt (by intro offset inside; rfl)
  obtain ⟨room,answer,records,globals,frame⟩ := after_count_normal ready inner pointer length heap count items readyPointer readyCount readyItems countEq heapGlobal heapBound before sizeBound arena.code value continuation
  have fields:=evaluation_fields ready inner afterCount (some (.returned value)) continuation
  have inputFrame:=Window.bytes_before ready inner heap.toNat (heap.toNat+16*count.toNat) pointer length frame before fits fields.1 fields.2.1
  have innerItems:=ListItems.transport ready inner pointer length.toNat items readyItems length.isLt inputFrame
  have finalItems:=ListItems.transport inner target pointer length.toNat items innerItems length.isLt (by intro offset inside; rw [restored]; rfl)
  have finalGlobals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64)))) := by
    rw [restored]
    exact globals
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
  refine ⟨items,count,finalItems,countEq,countBound,answer,?_,room,finalArena,finalGlobals,?_,priced⟩
  · rw [restored]; exact records
  · intro query outside
    rw [restored]
    exact frame query outside

end InitECandidate.Solver.Rlp.CurrentSlices

#print axioms InitECandidate.Solver.Rlp.CurrentSlices.body_normal
