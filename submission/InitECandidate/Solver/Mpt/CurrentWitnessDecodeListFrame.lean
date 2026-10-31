import InitECandidate.Solver.Mpt.CurrentWitnessDecodePairFrame
import InitECandidate.Solver.Mpt.CurrentWitnessDecodeAfterSlices
import InitECandidate.Solver.Mpt.CurrentWitnessDecodeSlices
import InitECandidate.Solver.Mpt.WitnessDecodeBranchView
import InitECandidate.Solver.Rlp.CurrentSlicesPersistentFrame

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Every actual successful list shape supplies its physical result.
The seventeen-item case initializes the genuine branch and pending record. -/
theorem current_after_array_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db array pointer heap count parentPointer parentLength cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (countEq : count.toNat=items.length)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (physical : Rlp.Validation.Arena source cursor limit)
    (dbBefore : db.toNat≤heap.toNat)
    (parentBound : parentLength.toNat≤1024) (parentLower : 2701131776≤parentPointer.toNat)
    (parentBefore : parentPointer.toNat+parentLength.toNat≤db.toNat)
    (payloadLower : parentPointer.toNat≤pointer.toNat) (payloadUpper : pointer.toNat+bytes≤parentPointer.toNat+parentLength.toNat)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterArray=(some (.returned value),post)) :
    LiveFrame source post heap cursor limit ∧ NormalResult post db parentPointer parentLength array cursor limit value := by
  rw [after_array_select source array count sliceCell] at normal
  by_cases two : count=2#64
  · rw [if_pos two] at normal
    have length : items.length=2:=by rw [←countEq,two]; rfl
    exact current_pair_frame source post db array parentPointer parentLength pointer heap cursor limit bytes items rows length
      arrayCell pointerCell lengthCell heapCell heapArena heapBound aligned live physical beforeArray dbBefore
      parentBound parentLower parentBefore payloadLower payloadUpper value normal
  · rw [if_neg two] at normal
    obtain ⟨valueEq,view,before,scratch,cell,allocation,nextAligned,grows,decreases,nextBound,frame⟩:=branch_view_normal source post
      db array parentPointer parentLength count pointer heap cursor limit bytes items rows countEq arrayCell pointerCell lengthCell sliceCell
      heapCell heapArena aligned live physical beforeArray parentBound parentLower parentBefore payloadLower payloadUpper value normal
    have initial:=branch_empty_normal source post array parentPointer parentLength count heap cursor limit arrayCell pointerCell lengthCell sliceCell
      heapCell heapArena aligned live physical value normal
    refine ⟨frame,?_⟩
    rw [valueEq]
    exact .record (branchDescription array parentPointer parentLength pointer bytes items heap) (PersistentAlloc.rounded heap 176#64)
      view rfl rfl before (Nat.le_refl _) (by change array.toNat≤heap.toNat; omega) (by constructor <;> rfl) initial
      cell allocation nextAligned scratch decreases

theorem current_after_slices_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db array pointer heap count parentPointer parentLength cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (countEq : count.toNat=items.length)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (physical : Rlp.Validation.Arena source cursor limit)
    (dbBefore : db.toNat≤heap.toNat)
    (parentBound : parentLength.toNat≤1024) (parentLower : 2701131776≤parentPointer.toNat)
    (parentBefore : parentPointer.toNat+parentLength.toNat≤db.toNat)
    (payloadLower : parentPointer.toNat≤pointer.toNat) (payloadUpper : pointer.toNat+bytes≤parentPointer.toNat+parentLength.toNat)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterSlices=(some (.returned value),post)) :
    LiveFrame source post heap cursor limit ∧ NormalResult post db parentPointer parentLength array cursor limit value := by
  rw [after_slices_array_shape] at normal
  obtain ⟨inner,continued,endpoint⟩:=ScalarScope.declare_trace source post "arr" (field "sl" 0) array afterArray _
    (slices_array_read source array count sliceCell) normal
  let entered:=bind source "arr" array
  have currentRows : Rows entered array pointer bytes items:=rows.frame source entered array pointer bytes items rfl (by intros; rfl)
  obtain ⟨frame,result⟩:=current_after_array_frame entered inner db array pointer heap count parentPointer parentLength cursor limit bytes items currentRows countEq
    ((bind_lookup_other source "arr" "sl" array (by decide)).trans sliceCell) (bind_lookup_same _ _ _)
    ((bind_lookup_other source "arr" "p" array (by decide)).trans pointerCell)
    ((bind_lookup_other source "arr" "n" array (by decide)).trans lengthCell)
    beforeArray heapCell heapArena heapBound aligned (live.of_frame rfl) (physical.of_fields source entered cursor limit rfl rfl)
    dbBefore parentBound parentLower parentBefore payloadLower payloadUpper value continued
  exact ⟨LiveFrame.of_erase entered inner source post heap cursor limit frame rfl (by rw [endpoint]; rfl),
    result.of_fields inner post db parentPointer parentLength array cursor limit value (by rw [endpoint]; rfl)
      (by rw [endpoint]; rfl) (by rw [endpoint]; rfl)⟩

/-- The converter supplies its own physical slice array and allocator
frontier before actual pair or branch decoding. Both stages protect earlier input
and older scratch records, while pending outcomes retain real progress. -/
theorem current_slices_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer header payload flag heap parentPointer parentLength cursor limit : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (small : payload.toNat≤1024) (before : (pointer+header).toNat+payload.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (physical : Rlp.Validation.Arena source cursor limit)
    (dbBefore : db.toNat≤heap.toNat)
    (parentBound : parentLength.toNat≤1024) (parentLower : 2701131776≤parentPointer.toNat)
    (parentBefore : parentPointer.toNat+parentLength.toNat≤db.toNat)
    (payloadLower : parentPointer.toNat≤(pointer+header).toNat)
    (payloadUpper : (pointer+header).toNat+payload.toNat≤parentPointer.toNat+parentLength.toNat)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source slicesCall=(some (.returned value),post)) :
    LiveFrame source post heap cursor limit ∧ NormalResult post db parentPointer parentLength heap cursor limit value := by
  rw [slices_shape] at normal
  obtain ⟨funded,target,items,count,inner,model,countEq,countBound,records,room,nextArena,domain,endian,globals,window,metadata,above,clock,price,continued,endpoint⟩:=
    Rlp.CurrentSlices.scoped_normal source post (pointer+header) payload heap live heapCell heapBound before (by omega)
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
  have firstPersistent : PersistentNormalFrame source ready heap:=
    (Rlp.CurrentSlices.persistent_frame_of_return source target heap count heapArena room metadata window).of_erase source target source ready heap rfl rfl
  have domainEq:=MemoryMetadata.domain firstPersistent.metadata
  change ready.memaddrs=source.memaddrs at domainEq
  have currentPhysical : Rlp.Validation.Arena ready cursor limit:=
    ⟨domainEq.trans physical.domain,
      (firstPersistent.globals (ofString "scratch_ptr") (by decide)).trans physical.cursorGlobal,
      (firstPersistent.globals (ofString "frame_mem_ptr") (by decide)).trans physical.limitGlobal,
      physical.ordered,physical.aligned,physical.lower,physical.upper⟩
  have first:=LiveFrame.of_persistent source ready heap cursor limit live physical firstPersistent (above cursor limit physical)
  have grows : heap.toNat≤next.toNat:=by dsimp [next]; have h:=image.arrayBefore; omega
  obtain ⟨tail,result⟩:=current_after_slices_frame ready inner db heap (pointer+header) next count parentPointer parentLength cursor limit payload.toNat items
    currentRows countEq sl currentPointer currentLength image.arrayBefore image.heapCell image.nextArena image.nextBound image.nextAligned
    (nextArena.of_frame rfl) currentPhysical (dbBefore.trans grows) parentBound parentLower parentBefore payloadLower payloadUpper value continued
  have complete:=LiveFrame.compose source ready inner heap cursor next cursor limit first tail grows (Nat.le_refl _)
  exact ⟨LiveFrame.of_erase source inner source post heap cursor limit complete rfl (by rw [endpoint]; rfl),
    result.of_fields inner post db parentPointer parentLength heap cursor limit value (by rw [endpoint]; rfl)
      (by rw [endpoint]; rfl) (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_array_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_slices_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_slices_frame
