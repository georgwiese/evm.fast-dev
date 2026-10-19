import InitECandidate.Solver.Rlp.SlicesAfterCountNormal
import InitECandidate.Solver.Rlp.SlicesNormalFrames
import InitECandidate.Solver.Rlp.ListCountCallItems
import InitECandidate.Solver.Rlp.SlicesCost

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete actual original list-to-slices return: derive the ordered
validated input, real record array, exact count, allocator room, retained
arena, actual next heap cursor and combined scratch/array memory footprint.
Current heap/input ownership and arena geometry still require reachability. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ items : List ListItem,∃ count : BitVec 64,
      ListItems target pointer length.toNat items ∧ count.toNat=items.length ∧ count.toNat≤length.toNat ∧
      value=result heap count ∧ Records target.memory heap pointer items ∧ heap.toNat+16*count.toNat≤33806089496 ∧
      Validation.Arena target cursor limit ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (count*16#64)))) ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+16*count.toNat≤query.toNat →
        target.memory query=source.memory query) ∧ source.clock-target.clock≤71*length.toNat+34 := by
  have fits : pointer.toNat+length.toNat<2^64 := by have := heap.isLt; omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  obtain ⟨positive,calleePost,items,count,inner,itemModel,countEq,nextArena,above,codeEq,heapEq,price,continuation,restored⟩ :=
    ListCount.scoped_normal_items source target pointer length cursor limit cutoff "count" arguments afterCount args arena fits aligned scratchBelow inputAbove installed value
      (by rw [←body_shape]; exact normal)
  let ready := bind {calleePost with locals:=source.locals} "count" count
  have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ "count" "p" _ (by decide)).trans pointerCell
  have readyCount : ready.locals.lookup (ofString "count")=some (.val (.word count)) := bind_lookup_same _ _ _
  have readyItems := ListItems.transport calleePost ready pointer length.toNat items itemModel length.isLt (by intro offset inside; rfl)
  have readyArena := Validation.Arena.of_fields calleePost ready cursor limit nextArena rfl rfl
  have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := heapEq.trans heapGlobal
  have readyInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed calleePost.code; rw [codeEq]; exact installed
  obtain ⟨room,answer,records,globals,frame⟩ := after_count_normal ready inner pointer length heap count items readyPointer readyCount readyItems countEq readyHeap heapBound before sizeBound readyInstalled value continuation
  have fields := Input.evaluation_fields ready inner afterCount (some (.returned value)) continuation
  have inputFrame := Window.bytes_before ready inner heap.toNat (heap.toNat+16*count.toNat) pointer length frame before fits fields.1 fields.2.1
  have innerItems := ListItems.transport ready inner pointer length.toNat items readyItems length.isLt inputFrame
  have finalItems := ListItems.transport inner target pointer length.toNat items innerItems length.isLt (by intro offset inside; rw [restored]; rfl)
  have innerArena := Validation.Arena.heap_updated ready inner cursor limit (PersistentAlloc.rounded heap (count*16#64)) readyArena fields.1 globals
  have finalArena := Validation.Arena.of_fields inner target cursor limit innerArena (by rw [restored]; rfl) (by rw [restored]; rfl)
  have finalHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (count*16#64)))) := by
    rw [restored]
    change inner.globals.lookup (ofString "heap_ptr")=_
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  have countBound := ListItems.count_le calleePost pointer length.toNat items itemModel
  rw [←countEq] at countBound
  have priced := body_cost source pointer length cursor limit pointerCell lengthCell arena fits installed
  rw [normal] at priced
  refine ⟨items,count,finalItems,countEq,countBound,answer,?_,room,finalArena,finalHeap,?_,priced⟩
  · rw [restored]
    exact records
  · intro query beyond outside
    rw [restored]
    exact (frame query outside).trans (above query beyond)

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.body_normal
