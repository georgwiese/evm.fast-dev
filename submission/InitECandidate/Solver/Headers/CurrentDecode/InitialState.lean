import InitECandidate.Solver.Headers.CurrentDecode.Allocation
import InitECandidate.Solver.Headers.CurrentPipeline.State

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- The real canonical count/allocation entry supplies the initial pipeline
state. Its record image,21/23 count, allocation room and alignment must come
from the reached parser/allocator prefix, with no future field result. -/
theorem allocation_state (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header count : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (data : CurrentHelpers.SliceImage source pointer array bytes items)
    (countEq : count.toNat=items.length) (countValid : count=21#64 ∨ count=23#64)
    (before : array.toNat+16*items.length≤header.toNat)
    (room : header.toNat+248≤2952790016) (aligned : header.toNat%8=0) :
    CurrentPipeline.State (allocationEntry source array count header) pointer array header
      (if count=23#64 then 1#64 else 0#64) bytes items [] := by
  let base:=counted (declared source array count) count
  let ready:=allocationEntry source array count header
  have baseFrame : LocalEffects.erase base=LocalEffects.erase source := (counted_frame source array count).1
  have baseArena : CurrentStartup.ArenaState base := data.arena.of_frame baseFrame
  have readyArena : CurrentStartup.ArenaState ready := by
    refine ⟨?_,?_,baseArena.domain,baseArena.code⟩
    · change (base.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded header 248#64)))).lookup (ofString "scratch_ptr")=_
      simpa [HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide] using baseArena.scratch
    · change (base.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded header 248#64)))).lookup (ofString "frame_mem_ptr")=_
      simpa [HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide] using baseArena.frame
  obtain ⟨headerCell,arrayCell,countCell,currentCell,heapCell,memory,clock⟩:=allocation_fields source array count header
  have nextItems:=Rlp.ListItems.transport source ready pointer bytes items data.itemsAtInput (by have h:=data.inputFits; omega)
    (by intro offset inside
        change Rlp.ReadLength.byte (LocalEffects.erase source) _=Rlp.ReadLength.byte (LocalEffects.erase base) _
        rw [baseFrame])
  have nextRecords : Rlp.Slices.Records ready.memory array pointer items := by
    rw [memory]
    exact data.records
  have slices : CurrentHelpers.SliceImage ready pointer array bytes items :=
    ⟨nextItems,nextRecords,readyArena,data.arrayArena,data.arrayAligned,data.inputFits,data.inputBefore⟩
  have branch : ((if count=23#64 then 1#64 else 0#64) : BitVec 64)=0#64 ∧ items.length=21 ∨
      ((if count=23#64 then 1#64 else 0#64) : BitVec 64)=1#64 ∧ items.length=23 := by
    rcases countValid with parent|current
    · rw [parent] at countEq ⊢
      exact Or.inl ⟨by decide,countEq.symm⟩
    · rw [current] at countEq ⊢
      exact Or.inr ⟨by decide,countEq.symm⟩
  exact ⟨slices,Slots.empty ready,arrayCell,headerCell,currentCell,branch,
    ⟨by have low:=data.arrayArena.lower; omega,by omega⟩,aligned,before,heapCell⟩

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.allocation_state
