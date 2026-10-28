import InitECandidate.Solver.Mpt.CurrentWitnessDecodeAfterSlices
import InitECandidate.Solver.Rlp.CurrentSlicesReachedCost
import InitECandidate.Solver.Rlp.CurrentSlicesCall

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Facts obtained from the actual converter's successful allocation, kept
separate from the larger ordinary readable memory domain. -/
structure CurrentSliceImage (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length count : BitVec 64) (items : List Rlp.ListItem) : Prop where
  rows : Rows source array pointer length.toNat items
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded array (count*16#64))))
  nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded array (count*16#64)) 0
  nextBound : (PersistentAlloc.rounded array (count*16#64)).toNat≤2952790016
  nextAligned : (PersistentAlloc.rounded array (count*16#64)).toNat%8=0
  arrayBefore : array.toNat+16*items.length≤(PersistentAlloc.rounded array (count*16#64)).toNat

theorem current_slice_image (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap count : BitVec 64) (items : List Rlp.ListItem)
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (small : length.toNat≤1024)
    (model : Rlp.ListItems target pointer length.toNat items) (countEq : count.toNat=items.length)
    (countBound : count.toNat≤length.toNat) (records : Rlp.Slices.Records target.memory heap pointer items)
    (room : heap.toNat+16*count.toNat≤2952790016) (arena : CurrentStartup.ArenaState target)
    (globals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64))))) :
    CurrentSliceImage target heap pointer length count items := by
  have amountNumber : (count*16#64).toNat=16*count.toNat := by
    rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by change count.toNat*16<2^64; omega)]
    change count.toNat*16=16*count.toNat
    omega
  have checked:=PersistentAlloc.guards heap (count*16#64) (by rw [amountNumber]; exact room)
  have grows:=checked.2.2.1
  rw [amountNumber,countEq] at grows
  have allocation : AllocatedBytes.Arena heap (16*items.length) :=
    ⟨heapArena.lower,by rw [←countEq]; omega⟩
  refine ⟨Rows.of_model target heap pointer length.toNat items arena.domain model records allocation aligned
    (by have h:=heap.isLt; omega),?_,?_,checked.2.2.2.1,checked.2.2.2.2,grows⟩
  · rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  · exact ⟨by have lower:=heapArena.lower; omega,by have upper:=checked.2.2.2.1; omega⟩

theorem slices_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag)) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) slicesArguments=
      some (Rlp.Header.values (pointer+header) payload) := by
  simp [slicesArguments,field,localVar,toExact,evalListHOLFinite,evalListHOLExact,evalHOLExact,itemCell,Rlp.Item.result,Rlp.Header.values]

/-- Price the real converter continuation with its own allocated physical
rows. Failed calls or allocations are already covered by the front allowance. -/
theorem current_slices_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag heap : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (small : payload.toNat≤1024) (before : (pointer+header).toNat+payload.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source slicesCall).2.clock≤payload.toNat/4+149*payload.toNat+270 := by
  rw [slices_shape]
  have price:=Rlp.CurrentSlices.scoped_frame_cost source (pointer+header) payload heap arena heapCell heapBound before (by omega)
    "sl" slicesArguments afterSlices (payload.toNat/4+92*payload.toNat+266)
    (slices_arguments_read source pointer header payload flag itemCell) (by
      intro target items count model countEq countBound records room nextArena domain endian globals
      have image:=current_slice_image source target (pointer+header) payload heap count items heapArena aligned before small
        model countEq countBound records room nextArena globals
      let ready:=CallNormal.continuationEntry source target "sl" (Rlp.Slices.result heap count)
      have currentRows : Rows ready heap (pointer+header) payload.toNat items :=
        image.rows.frame target ready heap (pointer+header) payload.toNat items rfl (by intros; rfl)
      have sl : ready.locals.lookup (ofString "sl")=some (Rlp.Slices.result heap count) := CallNormal.continuation_lookup_same source target "sl" _
      exact current_after_slices_price ready heap (pointer+header) (PersistentAlloc.rounded heap (count*16#64)) count payload.toNat items
        currentRows countEq sl small image.arrayBefore image.heapCell image.nextArena image.nextBound image.nextAligned (nextArena.of_frame rfl))
  exact Nat.le_trans price (by omega)

theorem current_slices_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag heap : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (small : payload.toNat≤1024) (before : (pointer+header).toNat+payload.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) : ReturnFacts.Returns source slicesCall ZeroResult := by
  intro post value normal
  rw [slices_shape] at normal
  obtain ⟨positive,target,items,count,inner,model,countEq,countBound,records,room,nextArena,domain,endian,globals,frame,clock,price,continued,restored⟩:=
    Rlp.CurrentSlices.scoped_normal source post (pointer+header) payload heap arena heapCell heapBound before (by omega)
      "sl" slicesArguments afterSlices (slices_arguments_read source pointer header payload flag itemCell) value normal
  have image:=current_slice_image source target (pointer+header) payload heap count items heapArena aligned before small
    model countEq countBound records room nextArena globals
  let ready:=CallNormal.continuationEntry source target "sl" (Rlp.Slices.result heap count)
  have currentRows : Rows ready heap (pointer+header) payload.toNat items :=
    image.rows.frame target ready heap (pointer+header) payload.toNat items rfl (by intros; rfl)
  have sl : ready.locals.lookup (ofString "sl")=some (Rlp.Slices.result heap count) := CallNormal.continuation_lookup_same source target "sl" _
  exact current_after_slices_zero ready heap (pointer+header) count payload.toNat items currentRows countEq sl
    (nextArena.of_frame rfl) inner value continued

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_slice_image
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_slices_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_slices_zero
