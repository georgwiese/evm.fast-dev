import InitECandidate.Solver.Mpt.CurrentWitnessDecodePairFrame
import InitECandidate.Solver.Mpt.CurrentWitnessDecodeAfterSlices
import InitECandidate.Solver.Mpt.CurrentWitnessDecodeSlices
import InitECandidate.Solver.Rlp.CurrentSlicesPersistentFrame

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem current_after_array_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap count parentPointer parentLength : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (countEq : count.toNat=items.length)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (small : bytes≤1024) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterArray=(some (.returned value),post)) :
    TerminalResult heap value ∧ PersistentNormalFrame source post heap := by
  rw [after_array_select source array count sliceCell] at normal
  by_cases two : count=2#64
  · rw [if_pos two] at normal
    have length : items.length=2:=by rw [←countEq,two]; rfl
    obtain ⟨first,second,rfl⟩:=two_items items length
    exact current_pair_frame source post array pointer heap parentPointer parentLength bytes [first,second] first second rows rfl rfl
      arrayCell pointerCell lengthCell small beforeArray heapCell heapArena heapBound aligned arena value normal
  · rw [if_neg two] at normal
    exact (branch_body_no_return source post arena value normal).elim

theorem current_after_slices_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap count parentPointer parentLength : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (countEq : count.toNat=items.length)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (small : bytes≤1024) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterSlices=(some (.returned value),post)) :
    TerminalResult heap value ∧ PersistentNormalFrame source post heap := by
  rw [after_slices_array_shape] at normal
  obtain ⟨inner,continued,endpoint⟩:=ScalarScope.declare_trace source post "arr" (field "sl" 0) array afterArray _
    (slices_array_read source array count sliceCell) normal
  let entered:=bind source "arr" array
  have currentRows : Rows entered array pointer bytes items:=rows.frame source entered array pointer bytes items rfl (by intros; rfl)
  obtain ⟨nodeResult,frame⟩:=current_after_array_frame entered inner array pointer heap count parentPointer parentLength bytes items currentRows countEq
    ((bind_lookup_other source "arr" "sl" array (by decide)).trans sliceCell) (bind_lookup_same _ _ _)
    ((bind_lookup_other source "arr" "p" array (by decide)).trans pointerCell)
    ((bind_lookup_other source "arr" "n" array (by decide)).trans lengthCell)
    small beforeArray heapCell heapArena heapBound aligned (arena.of_frame rfl) value continued
  exact ⟨nodeResult,frame.of_erase entered inner source post heap rfl (by rw [endpoint]; rfl)⟩

/-- The converter supplies its own physical slice array and allocator
frontier before normal two-item decoding. Both fresh stages protect the same
original input, runtime state and nonheap globals. -/
theorem current_slices_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag heap parentPointer parentLength : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (small : payload.toNat≤1024) (before : (pointer+header).toNat+payload.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source slicesCall=(some (.returned value),post)) :
    TerminalResult heap value ∧ PersistentNormalFrame source post heap := by
  rw [slices_shape] at normal
  obtain ⟨funded,target,items,count,inner,model,countEq,countBound,records,room,nextArena,domain,endian,globals,window,metadata,clock,price,continued,endpoint⟩:=
    Rlp.CurrentSlices.scoped_normal source post (pointer+header) payload heap arena heapCell heapBound before (by omega)
      "sl" slicesArguments afterSlices (slices_arguments_read source pointer header payload flag itemCell) value normal
  have image:=current_slice_image source target (pointer+header) payload heap count items heapArena aligned before small
    model countEq countBound records room nextArena globals
  let ready:=CallNormal.continuationEntry source target "sl" (Rlp.Slices.result heap count)
  let next:=PersistentAlloc.rounded heap (count*16#64)
  have currentRows : Rows ready heap (pointer+header) payload.toNat items:=image.rows.frame target ready heap (pointer+header) payload.toNat items rfl (by intros; rfl)
  have sl : ready.locals.lookup (ofString "sl")=some (Rlp.Slices.result heap count):=CallNormal.continuation_lookup_same _ _ _ _
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word parentPointer)):=
    (CallNormal.continuation_lookup_other source target "sl" "p" _ (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word parentLength)):=
    (CallNormal.continuation_lookup_other source target "sl" "n" _ (by decide)).trans lengthCell
  obtain ⟨nodeResult,tail⟩:=current_after_slices_frame ready inner heap (pointer+header) next count parentPointer parentLength payload.toNat items
    currentRows countEq sl currentPointer currentLength small image.arrayBefore image.heapCell image.nextArena image.nextBound image.nextAligned
    (nextArena.of_frame rfl) value continued
  have first : PersistentNormalFrame source ready heap:=
    (Rlp.CurrentSlices.persistent_frame_of_return source target heap count heapArena room metadata window).of_erase source target source ready heap rfl rfl
  have grows : heap.toNat≤next.toNat:=by dsimp [next]; have h:=image.arrayBefore; omega
  have complete:=first.trans source ready inner heap next tail grows
  exact ⟨nodeResult.mono heap next grows,complete.of_erase source inner source post heap rfl (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_array_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_slices_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_slices_frame
